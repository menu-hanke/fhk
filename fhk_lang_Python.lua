-- CPython 3.x stable ABI model caller for both python/non-python hosts.
-- see:
-- * https://peps.python.org/pep-0384/
-- * https://docs.python.org/3/c-api/stable.html#stable-abi-list

local driver = require "fhk_driver"
local ffi = require "ffi"

-- Stable ABI.
ffi.cdef [[
typedef struct PyObject PyObject;
typedef ssize_t Py_ssize_t;
int Py_IsInitialized();
void Py_InitializeEx(int);
void Py_Finalize();
void Py_DecRef(PyObject *);
void Py_IncRef(PyObject *);
PyObject *PyErr_Occurred();
void PyErr_Fetch(PyObject **, PyObject **, PyObject **);
PyObject *PyObject_Str(PyObject *);
PyObject *PyObject_GetItem(PyObject *, PyObject *);
PyObject *Py_BuildValue(const char *, ...);
const char *PyUnicode_AsUTF8AndSize(PyObject *, Py_ssize_t *);
PyObject *PyUnicode_DecodeFSDefault(const char *);
PyObject *PyDict_New();
PyObject *PyDict_GetItemString(PyObject *, const char *);
PyObject *PyTuple_New(Py_ssize_t);
PyObject *PyTuple_GetItem(PyObject *, Py_ssize_t);
int PyTuple_SetItem(PyObject *, Py_ssize_t, PyObject *);
PyObject *PyLong_FromLong(long);
PyObject *PyLong_FromSsize_t(Py_ssize_t);
PyObject *PyLong_FromSize_t(size_t);
long PyLong_AsLong(PyObject *);
PyObject *PyFloat_FromDouble(double);
double PyFloat_AsDouble(PyObject *);
PyObject *PyBool_FromLong(long);
PyObject *PyImport_Import(PyObject *);
int Py_IsNone(const PyObject *);
PyObject *PyObject_GetAttrString(PyObject *, const char *);
PyObject *PyObject_Call(PyObject *, PyObject *, PyObject *);
PyObject *PyObject_CallNoArgs(PyObject *);
PyObject *PyObject_CallMethodObjArgs(PyObject *, PyObject *, ...);
PyObject *Py_CompileString(const char *, const char *, int);
PyObject *PyEval_EvalCode(PyObject *, PyObject *, PyObject *);
PyObject *PyEval_GetBuiltins();
PyObject *PyMemoryView_FromMemory(char *, Py_ssize_t, int);
]]

local PyBUF_READ = 0x100
local Py_file_input = 257

-- TODO: if we need type conversion inside a vector, eg. memoryview[int] -> List[Enum],
-- that should go here as a *python* function.
local py_src = [[
from collections.abc import Iterable, Sequence
from functools import wraps
from inspect import Signature, signature
from typing import Tuple, Union, get_origin, get_args
def _optional(t):
	@wraps(t)
	def w(x):
		try:
			return t(x)
		except:
			return None
	return w
def _getparam(ann):
	if ann is Signature.empty:
		return None, None
	if ann == memoryview:
		return None, memoryview
	orig = get_origin(ann)
	if orig is None:
		return ann, None
	args = get_args(ann)
	if orig == Union:
		if len(args) == 2:
			none = 0 if args[0] == type(None) else (1 if args[1] == type(None) else None)
			if none is not None:
				t, v = _getparam(args[none^1])
				if t is not None:
					t = _optional(t)
				return t, v
		return None, None
	if orig in (Iterable, Sequence):
		orig = memoryview
	if len(args) == 1:
		return args[0], orig
	return None, None
def _isvec(ann):
	if ann is Signature.empty:
		return None
	orig = get_origin(ann)
	if orig is not None and len(get_args(ann)) == 1:
		return orig
def sig(f, np, nr):
	pt, pv, rv = [None]*np, [None]*np, [None]*nr
	s = signature(f)
	for i,p in zip(range(np), s.parameters.values()):
		pt[i], pv[i] = _getparam(p.annotation)
	ra = s.return_annotation
	if ra is not Signature.empty:
		if nr > 1:
			if issubclass(get_origin(ra), Tuple):
				for i,t in zip(range(nr), get_args(ra)):
					rv[i] = _isvec(t)
		else:
			rv[0] = _isvec(ra)
	return tuple(pt), tuple(pv), tuple(rv)
]]

-- init code to run when we are the ones setting up the python interpreter.
local py_hostinit = [[
import sys, os
sys.path.append(os.getcwd())
]]

local C = ffi.C
if not pcall(function() return C.Py_InitializeEx end) then
	-- libpython3 must be loaded with RTLD_GLOBAL.
	-- see: https://docs.python.org/3/whatsnew/3.8.html#changes-in-the-c-api
	C = ffi.load("python3", true)
	if not C then
		error("couldn't find python shared library")
	end
end

local function gco(o)
	if o ~= nil then
		return ffi.gc(o, C.Py_DecRef)
	end
end

local function gcoref(o)
	o = gco(o)
	if o then
		C.Py_IncRef(o)
	end
	return o
end

local function raise(err)
	err = err or "python error"
	if C.PyErr_Occurred() ~= nil then
		local e = ffi.new("PyObject *[3]")
		C.PyErr_Fetch(e+0, e+1, e+2)
		local s = gco(C.PyObject_Str(e[1]))
		if s then
			local size = ffi.new("Py_ssize_t[1]")
			local p = C.PyUnicode_AsUTF8AndSize(s, size)
			if p ~= nil then
				error(string.format("%s: %s", err, ffi.string(p, size[0])), 2)
			end
		end
	end
	error(err)
end

local function echeck3(a, b, c)
	if C.PyErr_Occurred() ~= nil then
		C.Py_DecRef(a)
		C.Py_DecRef(b)
		C.Py_DecRef(c)
		raise()
	end
end

local function ocheck(o, err)
	return o == nil and raise(err) or o
end

local function gcocheck(o, err)
	return ocheck(gco(o), err)
end

local function gcocheckref(o, err)
	return ocheck(gcoref(o), err)
end

-- intern list of argument tuples.
local pytuples = {}
local function tuple(n)
	if not pytuples[n] then
		local tuple = gco(C.PyTuple_New(n)) or raise()
		pytuples[n] = tuple
	end
	return pytuples[n]
end

local finalizer
if C.Py_IsInitialized() == 0 then
	-- if we init python, we'll close it as well.
	-- this could blow up if someone inits python after us, but oh well.
	-- this works in most cases.
	finalizer = newproxy(true)
	getmetatable(finalizer).__gc = function() C.Py_Finalize() end
	C.Py_InitializeEx(0)
	local code = gcocheck(C.Py_CompileString(py_hostinit, "<fhk-hostinit>", Py_file_input))
	local globals = gcocheck(C.PyDict_New())
	C.Py_DecRef(C.PyEval_EvalCode(code, globals, nil))
	if C.PyErr_Occurred() ~= nil then raise() end
end

local pysig = (function()
	local code = gcocheck(C.Py_CompileString(py_src, "<fhk-init>", Py_file_input))
	local globals = gcocheck(C.PyDict_New())
	C.Py_DecRef(C.PyEval_EvalCode(code, globals, nil))
	if C.PyErr_Occurred() ~= nil then raise() end
	return ocheck(C.PyDict_GetItemString(globals, "sig"))
end)()

local function infersig(pf, np, nr)
	local args = gcocheck(C.Py_BuildValue("(Oii)", pf, ffi.cast("int", np), ffi.cast("int", nr)))
	local info = gcocheck(C.PyObject_Call(pysig, args, nil))
	local pt = ocheck(C.PyTuple_GetItem(info, 0))
	local pv = ocheck(C.PyTuple_GetItem(info, 1))
	local rv = ocheck(C.PyTuple_GetItem(info, 2))
	return pt, pv, rv
end

local builtins = (function()
	local b = C.PyEval_GetBuiltins()
	return {
		bool       = ocheck(C.PyDict_GetItemString(b, "bool")),
		int        = ocheck(C.PyDict_GetItemString(b, "int")),
		float      = ocheck(C.PyDict_GetItemString(b, "float")),
		memoryview = ocheck(C.PyDict_GetItemString(b, "memoryview"))
	}
end)()

local ctkind = {}
for k,v in pairs {
	bool    = "bool",
	float   = "float", double   = "float",
	int8_t  = "int",   uint8_t  = "int",
	int16_t = "int",   uint16_t = "int",
	int32_t = "int",   uint32_t = "int",
	int64_t = "int",   uint64_t = "int",
} do
	ctkind[tonumber(ffi.typeof(k))] = v
end

local ctconvf = {}
for k,v in pairs {
	bool     = "PyBool_FromLong",
	float    = "PyFloat_FromDouble", double   = "PyFloat_FromDouble",
	int8_t   = "PyLong_FromLong",    uint8_t  = "PyLong_FromLong",
	int16_t  = "PyLong_FromLong",    uint16_t = "PyLong_FromLong",
	int32_t  = "PyLong_FromLong",
	uint32_t = ffi.sizeof("long") > 4 and "PyLong_FromLong" or "PyLong_FromSize_t",
	int64_t  = ffi.sizeof("long") > 4 and "PyLong_FromLong" or "PyLong_FromSsize_t",
	uint64_t = "PyLong_FromSize_t",
} do
	ctconvf[tonumber(ffi.typeof(k))] = v
end

-- ctype -> python struct notation
-- see: https://docs.python.org/3/library/struct.html
local pyfmt = {}
for k,v in pairs {
	bool     = "?",
	float    = "f", double   = "d",
	int8_t   = "b", uint8_t  = "B",
	int16_t  = "h", uint16_t = "H",
	int32_t  = "i", uint32_t = "I",
	int64_t  = "q", uint64_t = "Q",
} do
	pyfmt[tonumber(ffi.typeof(k))] = gcocheck(C.PyUnicode_DecodeFSDefault(v))
end

local tup1 = gcocheck(C.PyTuple_New(1))
local function call1(x, a)
	C.PyTuple_SetItem(tup1, 0, a)
	return C.PyObject_Call(x, tup1, nil)
end

local py_cast = gcocheck(C.PyUnicode_DecodeFSDefault("cast"))
local function memoryview(p, size, fmt)
	local mv = ocheck(C.PyMemoryView_FromMemory(p, size, PyBUF_READ))
	local mc = ocheck(C.PyObject_CallMethodObjArgs(mv, py_cast, fmt, nil))
	C.Py_DecRef(mv)
	return mc
end

---- loader ----------------------------------------

local function ctcallerr(ctype)
	error(string.format("unsuitable ctype for python function call: %s", ctype), 2)
end

-- modcall python callable PyObject *
local function modcallpy(J, o, f)
	local mode = driver.getmode(o)
	local pt, pv, rv = infersig(f, #o.params, #o.returns)
	local code = driver.code()
	local uC = C == ffi.C and "C" or code:upval(C)
	code.upv.ocheck = ocheck
	code.upv.echeck3 = echeck3
	code.upv.cast = ffi.cast
	code.upv.f = f
	if #o.params > 0 then
		code.upv.args = tuple(#o.params)
		for i,p in ipairs(o.params) do
			local v = ocheck(C.PyTuple_GetItem(pv, i-1))
			local ctid = tonumber(p.var.ctype)
			code.src:put("do\n")
			if C.Py_IsNone(v) == 0 or mode:sub(i,i) == "v" then
				code.upv.memoryview = memoryview
				local fmt = code:upval(pyfmt[ctid] or ctcallerr(p.var.ctype))
				code.src:putf(
					"local x = memoryview(S.edges[%d].p, S.edges[%d].n*%d, %s)\n",
					i-1, i-1, ffi.sizeof(p.var.ctype), fmt
				)
				if C.Py_IsNone(v) == 0 and v ~= builtins.memoryview then
					local vec = code:upval(gcocheckref(v))
					code.upv.call1 = call1
					-- no need to decref: call1 eats the reference.
					code.src:putf("x = ocheck(call1(%s, x))\n", vec)
				end
			else
				local ctp = code:upval(ffi.typeof("$*", p.var.ctype))
				code.src:putf(
					"local x = ocheck(%s.%s(cast(%s, S.edges[%d].p)[0]))\n",
					uC, ctconvf[ctid] or ctcallerr(p.var.ctype), ctp, i-1
				)
				local t = ocheck(C.PyTuple_GetItem(pt, i-1))
				local kind = ctkind[ctid] or ctcallerr(p.var.ctype)
				if t ~= builtins[kind] and C.Py_IsNone(t) == 0 then
					local tconv = code:upval(gcocheckref(t))
					code.upv.call1 = call1
					-- no need to decref: call1 eats the reference
					code.src:putf("x = ocheck(call1(%s, x))\n", tconv)
				end
			end
			-- PyTuple_SetItem steals our ref, no need for decref here.
			code.src:putf("%s.PyTuple_SetItem(args, %d, x)\n", uC, i-1)
			code.src:put("end\n")
		end
		code.src:putf("local r = ocheck(%s.PyObject_Call(f, args, nil))\n", uC)
	else
		code.src:putf("local r = ocheck(%s.PyObject_CallNoArgs(f))\n", uC)
	end
	if #o.returns == 1 then
		code.src:put("local y = r\n")
	end
	for i,r in ipairs(o.returns) do
		code.src:put("do\n")
		local ctp = code:upval(ffi.typeof("$*", r.var.ctype))
		code.src:putf("local rp = cast(%s, S.edges[%d].p)\n", ctp, #o.params+i-1)
		if #o.returns > 1 then
			code.src:putf([[
				local y = %s.PyTuple_GetItem(r, %d)
				if y == nil then echeck3(r) end
			]], uC, i-1)
			code.src:putf("", uC, i-1)
		end
		local v = ocheck(C.PyTuple_GetItem(rv, i-1))
		local isvec = C.Py_IsNone(v) == 0 or mode:sub(#o.params+i,#o.params+i) == "v"
		local ctid = tonumber(r.var.ctype)
		local kind = ctkind[ctid] or ctcallerr(r.var.ctype)
		local dest, echeck, robj
		-- TODO: should specialize for common types (list?)
		-- TODO: just memcpy for buffer types (like numpy.array)
		if isvec then
			dest = "rp[i]"
			echeck = "echeck3(r, oi, robj)"
			robj = "robj"
			code.src:putf([[
				for i=0, tonumber(S.edges[%d].n)-1 do
					local oi = %s.PyLong_FromLong(i)
					if oi == nil then echeck3(r) end
					local robj = %s.PyObject_GetItem(y, oi)
					%s.Py_DecRef(oi)
					if robj == nil then echeck3(r) end
			]], #o.params+i-1, uC, uC, uC)
		else
			dest = "rp[0]"
			echeck = "echeck3(r)"
			robj = "y"
		end
		if kind == "float" then
			code.src:putf("local v = %s.PyFloat_AsDouble(%s)\n", uC, robj)
		elseif kind == "int" or kind == "bool" then
			code.src:putf("local v = %s.PyLong_AsLong(%s)\n", uC, robj)
		end
		code.src:putf("if v == -1 then %s end\n", echeck)
		code.src:putf("%s = v\n", dest)
		if isvec then
			code.src:putf([[
					%s.Py_DecRef(robj)
				end
			]], uC)
		end
		code.src:put("end\n")
	end
	code.src:putf("%s.Py_DecRef(r)\n", uC)
	code.name = string.format("=fhk:modcallpython<%s>", driver.desc(o))
	return code:emitjmp(J)
end

local function pyimportf(module, name)
	if not module then error("nil python module") end
	if not name then error("nil python name") end
	local pymodname = gcocheck(C.PyUnicode_DecodeFSDefault(module))
	local pymod = gcocheck(C.PyImport_Import(pymodname))
	return gcocheck(C.PyObject_GetAttrString(pymod, name))
end

local function py_load(J, o)
	local f = o.impl[1]
	if type(f) == "string" then
		f = pyimportf(f, o.impl[2])
	end
	return modcallpy(J, o, f)
end

--------------------------------------------------------------------------------

return {
	load        = py_load,
	_finalizer  = finalizer,
	-- for fhk_pyx
	raise       = raise,
	echeck3     = echeck3,
	ocheck      = ocheck,
	gcocheck    = gcocheck,
	gcocheckref = gcocheckref,
	tuple       = tuple,
	memoryview  = memoryview,
	builtins    = builtins,
	ctkind      = ctkind,
	ctconvf     = ctconvf,
	pyfmt       = pyfmt,
	call1       = call1
}
