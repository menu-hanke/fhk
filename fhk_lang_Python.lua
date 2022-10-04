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
void PyErr_NormalizeException(PyObject **, PyObject **, PyObject **);
int PyException_SetTraceback(PyObject *, PyObject *);
PyObject *PyObject_Str(PyObject *);
PyObject *PyObject_GetItem(PyObject *, PyObject *);
const char *PyUnicode_AsUTF8AndSize(PyObject *, Py_ssize_t *);
PyObject *PyUnicode_DecodeFSDefault(const char *);
PyObject *PyDict_New();
PyObject *PyDict_GetItemString(PyObject *, const char *);
PyObject *PyTuple_New(Py_ssize_t);
PyObject *PyTuple_GetItem(PyObject *, Py_ssize_t);
int PyTuple_SetItem(PyObject *, Py_ssize_t, PyObject *);
PyObject *PyLong_FromSsize_t(Py_ssize_t);
PyObject *PyLong_FromSize_t(size_t);
Py_ssize_t PyLong_AsSsize_t(PyObject *);
size_t PyLong_AsSize_t(PyObject *);
PyObject *PyFloat_FromDouble(double);
double PyFloat_AsDouble(PyObject *);
PyObject *PyBool_FromLong(long);
PyObject *PyImport_Import(PyObject *);
int Py_IsNone(const PyObject *);
PyObject *PyObject_GetAttrString(PyObject *, const char *);
PyObject *PyObject_Call(PyObject *, PyObject *, PyObject *);
PyObject *PyObject_CallNoArgs(PyObject *);
PyObject *PyObject_CallMethodObjArgs(PyObject *, PyObject *, ...);
PyObject *PyObject_CallFunction(PyObject *, const char *, ...);
PyObject *PyObject_CallFunctionObjArgs(PyObject *, ...);
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
from traceback import format_exception
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
def fmtexc(exc):
	return "".join(format_exception(exc))
]]

-- init code to run when we are the ones setting up the python interpreter.
local py_hostinit = [[
import sys, os
sys.path.append(os.getcwd())
]]

-- find the python C library.
-- on linux this is easy: if we are running inside a python interpreter, we don't need to do
-- anything. otherwise load libpython3.
-- on windows it's more involved: if we are running inside a python interpreter, we must
-- load the same dll as the python interpreter. otherwise load libpython3. except that it's
-- not always available (eg. on mingw), so we must instead load libpythonX.Y.dll. except
-- sometimes it may be called pythonXY.dll instead.
local C = ffi.C
if jit.os == "Windows" then
	-- https://learn.microsoft.com/en-us/windows/win32/winprog/windows-data-types
	-- https://learn.microsoft.com/en-us/windows/win32/api/psapi/nf-psapi-enumprocessmodules
	-- https://learn.microsoft.com/en-us/windows/win32/api/libloaderapi/nf-libloaderapi-getprocaddress
	ffi.cdef [[
	bool K32EnumProcessModules(void *, void **, uint32_t, uint32_t *);
	void *GetProcAddress(void *, const char *);
	uint32_t GetModuleFileNameA(void *, char *, uint32_t);
	]]
	local modules = ffi.new("void *[1024]")
	local msize = ffi.new("uint32_t[1]")
	local cproc = ffi.cast("void *", -1)
	if not C.K32EnumProcessModules(cproc, modules, 1024*8, msize) then
		error("EnumProcessModules() failed")
	end
	C = (function()
		for i=0, msize[0]/8-1 do
			if C.GetProcAddress(modules[i], "Py_InitializeEx") ~= nil then
				local buf = require("string.buffer").new()
				local p, n = buf:reserve(1024)
				local size = C.GetModuleFileNameA(modules[i], p, n)
				if size == 0 then
					error("GetModuleFileNameA() failed")
				end
				buf:commit(size+1)
				local dll = buf:get()
				return ffi.load(dll) or error(string.format("failed to load %s", dll))
			end
		end
		-- this will not work if only pythonXY is not installed or if it's called libpythonX.dll
		-- or whatever.
		-- but atleast it works for the default windows installation.
		return ffi.load("python3") or error("failed to load libpython3")
	end)()
else
	if not pcall(function() return C.Py_InitializeEx end) then
		-- libpython3 must be loaded with RTLD_GLOBAL.
		-- see: https://docs.python.org/3/whatsnew/3.8.html#changes-in-the-c-api
		C = ffi.load("python3", true) or error("failed to load libpython3")
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

local finalizer
if C.Py_IsInitialized() == 0 then
	-- if we init python, we'll close it as well.
	-- this could blow up if someone inits python after us, but oh well.
	-- this works in most cases.
	finalizer = newproxy(true)
	getmetatable(finalizer).__gc = function() C.Py_Finalize() end
	C.Py_InitializeEx(0)
	local code = assert(
		gco(C.Py_CompileString(py_hostinit, "<fhk-hostinit>", Py_file_input)),
		"failed to compile <fhk-hostinit>"
	)
	local globals = assert(gco(C.PyDict_New()), "PyDict_New() failed")
	C.Py_DecRef(C.PyEval_EvalCode(code, globals, nil))
	if C.PyErr_Occurred() ~= nil then error("python error in <fhk-hostinit>") end
end

local anchor, pysig, pyfmtexc = (function()
	local code = assert(
		gco(C.Py_CompileString(py_src, "<fhk-init>", Py_file_input)),
		"failed to compile <fhk-init>"
	)
	local globals = assert(gco(C.PyDict_New()), "PyDict_New() failed")
	C.Py_DecRef(C.PyEval_EvalCode(code, globals, nil))
	if C.PyErr_Occurred() ~= nil then error("python error in <fhk-init>") end
	local sig = assert(C.PyDict_GetItemString(globals, "sig"), "<fhk-init> didn't export `sig`")
	local fmtexc = assert(C.PyDict_GetItemString(globals, "fmtexc"), "<fhk-init> didn't export `fmtexc`")
	return {code=code, globals=globals}, sig, fmtexc
end)()

local function raise(err)
	err = err or "python error"
	if C.PyErr_Occurred() ~= nil then
		local e = ffi.new("PyObject *[3]")
		C.PyErr_Fetch(e+0, e+1, e+2)
		C.PyErr_NormalizeException(e+0, e+1, e+2)
		C.Py_DecRef(e[0])
		local value = gco(e[1])
		local tb = gco(e[2])
		if value then
			if tb then C.PyException_SetTraceback(value, tb) end
			local exc = assert(gco(C.PyObject_CallFunctionObjArgs(pyfmtexc, value, nil)),
				"yo dawg i heard u like errors")
			local size = ffi.new("Py_ssize_t[1]")
			local p = C.PyUnicode_AsUTF8AndSize(exc, size)
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
local tup1 = gcocheck(C.PyTuple_New(1))
local pytuples = {}
local function tuple(n)
	if not pytuples[n] then
		local tuple = gco(C.PyTuple_New(n)) or raise()
		pytuples[n] = tuple
	end
	return pytuples[n]
end

local function infersig(pf, np, nr)
	local info = gcocheck(C.PyObject_CallFunction(pysig, "Oii", pf, ffi.cast("int", np), ffi.cast("int", nr)))
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

local ctkindtab = {}
for k,v in pairs {
	bool    = "bool",
	float   = "float", double   = "float",
	int8_t  = "int",   uint8_t  = "uint",
	int16_t = "int",   uint16_t = "uint",
	int32_t = "int",   uint32_t = "uint",
	int64_t = "int",   uint64_t = "uint",
} do
	ctkindtab[tonumber(ffi.typeof(k))] = v
end

local function ctkind(ctype)
	return ctkindtab[tonumber(ctype)] or error(string.format("non-primitive ctype: %s", ctype))
end

-- C -> Python type conversion
local cpyconv = {
	bool  = "PyBool_FromLong",
	float = "PyFloat_FromDouble",
	int   = "PyLong_FromSsize_t",
	uint  = "PyLong_FromSize_t"
}

local function cpyconvf(ctype)
	return cpyconv[ctkind(ctype)]
end

-- Python -> C type conversion
local pycconv = {
	bool  = "PyLong_AsSsize_t",
	float = "PyFloat_AsDouble",
	int   = "PyLong_AsSsize_t",
	uint  = "PyLong_AsSize_t"
}

local function pycconvf(ctype)
	return pycconv[ctkind(ctype)]
end

-- ctype -> python struct notation
-- see: https://docs.python.org/3/library/struct.html
local fmttab = {}
for k,v in pairs {
	bool     = "?",
	float    = "f", double   = "d",
	int8_t   = "b", uint8_t  = "B",
	int16_t  = "h", uint16_t = "H",
	int32_t  = "i", uint32_t = "I",
	int64_t  = "q", uint64_t = "Q",
} do
	fmttab[tonumber(ffi.typeof(k))] = gcocheck(C.PyUnicode_DecodeFSDefault(v))
end

local function memfmt(ctype)
	return fmttab[tonumber(ctype)] or error(string.format("non-memoryview ctype: %s", ctype))
end

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
			code.src:put("do\n")
			if C.Py_IsNone(v) == 0 or mode:sub(i,i) == "v" then
				code.upv.memoryview = memoryview
				local fmt = code:upval(memfmt(p.var.ctype))
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
					uC, cpyconvf(p.var.ctype), ctp, i-1
				)
				local t = ocheck(C.PyTuple_GetItem(pt, i-1))
				local kind = ctkind(p.var.ctype)
				if t ~= builtins[kind == "uint" and "int" or kind] and C.Py_IsNone(t) == 0 then
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
		local dest, echeck, robj
		-- TODO: should specialize for common types (list?)
		-- TODO: just memcpy for buffer types (like numpy.array)
		if isvec then
			dest = "rp[i]"
			echeck = "echeck3(r, oi, robj)"
			robj = "robj"
			code.src:putf([[
				for i=0, tonumber(S.edges[%d].n)-1 do
					local oi = %s.PyLong_FromSsize_t(i)
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
		code.src:putf([[
			local v = %s.%s(%s)
			if v == -1 then %s end
			%s = v
		]], uC, pycconvf(r.var.ctype), robj, echeck, dest)
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
	-- must hold a reference to these two for as long as this module is loaded.
	_finalizer  = finalizer,
	_anchor     = anchor,
	-- for fhk_pyx
	C           = C,
	ocheck      = ocheck,
	gcocheckref = gcocheckref,
	echeck3     = echeck3,
	tuple       = tuple,
	builtins    = builtins,
	ctkind      = ctkind,
	pycconvf    = pycconvf,
	memfmt      = memfmt
}
