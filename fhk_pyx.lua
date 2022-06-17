local buffer = require "string.buffer"
local ffi = require "ffi"
local ctypes = require "fhk_ctypes"
local driver = require "fhk_driver"
local glib = require "fhk_g"
local lib = require "fhk_lib"
local rules = require "fhk_rules"
local C = require "fhk_clib"
local Py = require "fhk_lang_Python"
local ocheck, gcocheck, raise = Py.ocheck, Py.gcocheck, Py.raise

-- cython helpers, see _ctypes.pyx
ffi.cdef [[
fhk_subset fhk_pyx_tosubset(fhk_solver *, PyObject *);
]]

-- keep cdefs not used by the model caller here.
-- this file is only included on python host, while fhk_lang_Python is included
-- for all builds using the lua driver.
ffi.cdef [[
PyObject *PyDict_Items(PyObject *);
void Py_IncRef(PyObject *);
int PyObject_IsSubclass(PyObject *, PyObject *);
int PyObject_IsTrue(PyObject *);
int PyObject_SetAttr(PyObject *, PyObject *, PyObject *);
PyObject *PyDict_GetItem(PyObject *, PyObject *);
PyObject *PyList_GetItem(PyObject *, Py_ssize_t);
Py_ssize_t PyList_Size(PyObject *);
void *PyMem_Malloc(size_t);
void PyMem_Free(void *);
]]

local function tostr(o)
	local size = ffi.new("Py_ssize_t[1]")
	local p = C.PyUnicode_AsUTF8AndSize(o, size)
	if p == nil then raise() end
	return ffi.string(p, size[0])
end

local function gfuncctype(o)
	local ctype = gcocheck(C.PyObject_GetAttrString(o, "ctype"))
	if C.Py_IsNone(ctype) == 0 then return tostr(ctype) end
	local ptype = gcocheck(C.PyObject_GetAttrString(o, "type"))
	if C.PyObject_IsSubclass(ptype, Py.builtins.bool) == 1 then return "bool" end
	if C.PyObject_IsSubclass(ptype, Py.builtins.int) == 1 then return "int" end
	if C.PyObject_IsSubclass(ptype, Py.builtins.float) == 1 then return "double" end
end

local function tosubset(S, o)
	local ss = C.fhk_pyx_tosubset(S, o)
	if ss == ctypes.undefset then raise() end
	return ss
end

local function putjcall(fb, o)
	fb.upv.ocheck = ocheck
	fb.upv.f = gcocheck(C.PyObject_GetAttrString(o, "func"))
	local params = tostr(gcocheck(C.PyObject_GetAttrString(o, "params")))
	if #params > 0 then
		fb.upv.args = Py.tuple(#params)
		for i=1, #params do
			local p = params:sub(i,i)
			if p == "i" then
				fb.src:putf("C.PyTuple_SetItem(args, %d, ocheck(C.PyLong_FromLong(S.inst)))\n", i-1)
			elseif p == "x" then
				fb.src:putf([[
					C.Py_IncRef(X)
					C.PyTuple_SetItem(args, %d, X)
				]], i-1)
			end
		end
		fb.src:put("local r = ocheck(C.PyObject_Call(f, args, nil))\n")
	else
		fb.src:put("local r = ocheck(C.PyObject_CallNoArgs(f))\n")
	end
end

local function vrefpy(fb, op)
	putjcall(fb, op.o)
	fb.upv.cast = ffi.cast
	fb.upv.echeck3 = Py.echeck3
	local vector = gcocheck(C.PyObject_GetAttrString(op.o, "vector"))
	local havevec = C.Py_IsNone(vector) == 0
	local ctp = driver.upval(fb, ffi.typeof("$*", op.var.ctype))
	local dest, src, check
	if havevec then
		-- TODO: use fhk_setvalueC for directly copyable vectors
		dest, src = "vp[i]", "robj"
		check = "echeck3(r)"
		local subset = C.PyObject_IsTrue(gcocheck(C.PyObject_GetAttrString(op.o, "subset"))) == 1
		local obj
		if subset then
			obj = "x"
			fb.upv.iter = ctypes.iter
			fb.upv.tosubset = tosubset
			fb.src:putf([[
				local x = ocheck(C.PyTuple_GetItem(r, 0))
				local ss = tosubset(S, ocheck(C.PyTuple_GetItem(r, 1)))
				C.fhk_setvalueD(S, %d, ss)
				local vp = cast(%s, S.value.v[%d])
				local j = 0
				for i in iter(ss) do
					local oidx = C.PyLong_FromLong(j)
					j = j+1
			]], op.var.idx, ctp, op.var.idx)
		else
			obj = "r"
			-- TODO: the group index is known after layout,
			-- should save it in the graph instead.
			fb.upv.sizeofss = ctypes.sizeof
			fb.src:putf([[
				local ss = S.map[S.G.vars[%d].group].kmap
				local vp = cast(%s, C.fhk_setvalueD(S, %d, ss))
				for i=0, sizeofss(ss)-1 do
					local oidx = C.PyLong_FromLong(i)
			]], op.var.idx, ctp, op.var.idx)
		end
		fb.src:putf([[
					if oidx == nil then echeck3() end
					local robj = ocheck(C.PyObject_GetItem(%s, oidx))
					C.Py_DecRef(oidx)
		]], obj)
	else
		dest, src = "vp[0]", "r"
		check = "echeck3()"
		fb.src:putf("local vp = cast(%s, C.fhk_setvalueD(S, %d, S.inst))\n", ctp, op.var.idx)
	end
	local ctid = tonumber(op.var.ctype)
	local kind = Py.ctkind[ctid]
	if kind == "float" then
		fb.src:putf("local v = C.PyFloat_AsDouble(%s)\n", src)
	elseif kind == "int" or kind == "bool" then
		fb.src:putf("local v = C.PyLong_AsLong(%s)\n", src)
	end
	fb.src:putf([[
		C.Py_DecRef(%s)
		if v == -1 then %s end
		%s = v
	]], src, check, dest)
	if havevec then
		fb.src:put("end\n")
		fb.src:put("C.Py_DecRef(r)\n")
	end
	fb.name = string.format(
		"=fhk:vrefpy<%s>@%s",
		op.var.name,
		tostr(gcocheck(C.PyObject_GetAttrString(op.o, "desc")))
	)
end

local function mapcallpy(fb, op)
	fb.upv.tosubset = tosubset
	putjcall(fb, op.o)
	fb.src:put([[
		local ss = tosubset(S, r)
		C.Py_DecRef(r)
	]])
	if op.map.flags:match("i") then
		fb.src:putf("C.fhk_setmapI(S, %d, S.inst, ss)\n", op.map.idx)
	else
		fb.src:putf("C.fhk_setmapK(S, %d, ss)\n", op.map.idx)
	end
	fb.name = string.format(
		"=fhk:mapcallpy(%s)<%s>@%s",
		op.map.flags, op.map.name,
		tostr(gcocheck(C.PyObject_GetAttrString(op.o, "desc")))
	)
end

local function shapefpy(o)
	local params = tostr(gcocheck(C.PyObject_GetAttrString(o, "params")))
	local src = buffer.new()
	src:put("local C, f, ocheck, echeck3")
	if params == "x" then
		src:put(", call1")
	end
	src:put("= ...\n")
	src:put("return function(X)\n")
	if params == "x" then
		-- call1 eats the ref.
		src:put([[
			C.Py_IncRef(X)
			local r = ocheck(call1(f, X))
		]])
	else
		src:put("local r = ocheck(C.PyObject_CallNoArgs(f))\n")
	end
	src:put([[
		local v = C.PyLong_AsLong(r)
		C.Py_DecRef(r)
		if v == -1 then echeck3() end
		return v
		end
	]])
	local f = gcocheck(C.PyObject_GetAttrString(o, "func"))
	return load(src, "=fhk:shapefpy")(C, f, ocheck, Py.echeck3, Py.call1)
end

local function tolabels(o)
	local tab = {}
	local items = gcocheck(C.PyDict_Items(o))
	local num = tonumber(C.PyList_Size(items))
	for i=0, num-1 do
		local item = ocheck(C.PyList_GetItem(items, i))
		local k = tostr(ocheck(C.PyTuple_GetItem(item, 0)))
		local v = tonumber(C.PyLong_AsLong(ocheck(C.PyTuple_GetItem(item, 1))))
		if v == -1 then echeck3() end
		tab[k] = v
	end
	return tab
end

-- o :: ?
local function torules(o)
	local what = tostr(gcocheck(C.PyObject_GetAttrString(o, "what")))
	if what == "composite" then
		local rs = gcocheck(C.PyObject_GetAttrString(o, "rules"))
		local num = tonumber(C.PyList_Size(rs))
		local tab = {}
		for i=1, num do
			tab[i] = torules(ocheck(C.PyList_GetItem(rs, i-1)))
		end
		return rules.compose(tab)
	elseif what == "group" then
		return rules.group(
			tostr(gcocheck(C.PyObject_GetAttrString(o, "name"))),
			torules(gcocheck(C.PyObject_GetAttrString(o, "rule")))
		)
	elseif what == "named" then
		return rules.named(
			tostr(gcocheck(C.PyObject_GetAttrString(o, "name"))),
			torules(gcocheck(C.PyObject_GetAttrString(o, "rule")))
		)
	elseif what == "given(func)" then
		local cts = gfuncctype(o)
		return rules.tagged("var", function(_, event)
			if cts then event.setcts(cts) end
			event.setjfunc(function(fb, var) vrefpy(fb, {var=var, o=o}) end)
		end)
	elseif what == "map(func)" then
		local inverse = tostr(gcocheck(C.PyObject_GetAttrString(o, "inverse")))
		local flags = tostr(gcocheck(C.PyObject_GetAttrString(o, "flags")))
		return rules.tagged("map", function(_, event)
			event.setinverse(inverse)
			event.setflags(flags)
			event.setjfunc(function(fb, map) mapcallpy(fb, {map=map, o=o}) end)
		end)
	elseif what == "shape(num)" then
		return rules.shape(tonumber(C.PyLong_AsLong(gcocheck(C.PyObject_GetAttrString(o, "shape")))))
	elseif what == "shape(func)" then
		return rules.shape(shapefpy(o))
	elseif what == "label" then
		local labels = gcocheck(C.PyObject_GetAttrString(o, "labels"))
		return rules.label(tolabels(labels))
	elseif what == "edgerule" then
		local rule = tostr(C.PyObject_GetAttrString(o, "rule"))
		local map = gcocheck(C.PyObject_GetAttrString(o, "map"))
		local cts = gcocheck(C.PyObject_GetAttrString(o, "cts"))
		local rank = gcocheck(C.PyObject_GetAttrString(o, "rank"))
		return rules.edgerule(rule, {
			map = C.Py_IsNone(map) == 0 and tostr(map) or nil,
			cts = C.Py_IsNone(cts) == 0 and tostr(cts) or nil,
			rank = C.Py_IsNone(rank) == 0 and tostr(rank) or nil
		})
	else
		assert(false)
	end
end

-- o :: ?
local function pyx_new(o)
	return { state = rules.newstate(torules(ffi.cast("PyObject *", o))) }
end

-- o :: list[api#XRoot]
local function pyx_solver(fhk, o)
	o = ffi.cast("PyObject *", o)
	local num = tonumber(C.PyList_Size(o))
	local roots = {}
	for i=1, num do
		local oi = ocheck(C.PyList_GetItem(o, i-1))
		local var = tostr(gcocheck(C.PyObject_GetAttrString(oi, "var")))
		local ctype = gcocheck(C.PyObject_GetAttrString(oi, "ctype"))
		if C.Py_IsNone(ctype) == 0 then
			rules.typehint(fhk.state, var, tostr(ctype))
		end
		local constructor = gcocheck(C.PyObject_GetAttrString(oi, "constructor"))
		local vector = gcocheck(C.PyObject_GetAttrString(oi, "vector"))
		local havevec = C.Py_IsNone(vector) == 0
		local havetype = C.Py_IsNone(constructor) == 0
		if not (havevec or havetype) then
			vector = Py.builtins.memoryview
			havevec = true
		end
		roots[i] = {
			pyattr = gcocheck(C.PyObject_GetAttrString(oi, "attr")),
			var = rules.root(fhk.state, var),
			group = rules.getgroup(fhk.state, lib.groupof(var)),
			constructor = constructor,
			vector = vector,
			havetype = havetype,
			havevec = havevec
		}
	end
	table.insert(fhk, roots)
	return #fhk
end

local function getsubset(S, group, name, o)
	if o ~= nil then
		local ss = C.PyDict_GetItem(o, name)
		if ss == nil then
			if C.PyErr_Occurred() ~= nil then
				raise()
			end
		else
			return tosubset(S, ss)
		end
	end
	return S.map[group].kmap
end

local function cterr(ctype)
	error(string.format("non-primitive ctype: %d", ctype))
end

local function setattr(o, a, v)
	local r = C.PyObject_SetAttr(o, a, v)
	if r ~= 0 then raise() end
end

local function buildsolver(fb, roots, jump)
	fb.name = "=fhk: solver" -- TODO: maybe a more descriptive name?
	fb.upv.getsubset = getsubset
	fb.upv.sizeofss = ctypes.sizeof
	fb.upv.cast = ffi.cast
	fb.upv.ocheck = ocheck
	fb.upv.setattr = setattr
	fb.upv.jump = jump
	fb.src:put([[
		result = cast("PyObject *", result)
		subsets = subsets and cast("PyObject *", subsets)
	]])
	for i,r in ipairs(roots) do
		local attr = driver.upval(fb, r.pyattr)
		-- TODO: direct copy roots, eg. preallocated numpy arrays.
		if r.vector ~= Py.builtins.memoryview then
			fb.src:putf("local vp%d\n", i)
		end
		fb.src:put("do\n")
		fb.src:putf("local ss = getsubset(S, %d, %s, subsets)\n", r.group.idx, attr)
		fb.src:putf("local vp = C.fhk_setrootD(S, %d, ss)\n", r.var.idx)
		if r.havevec then
			fb.upv.memoryview = Py.memoryview
			local fmt = driver.upval(fb, Py.pyfmt[tonumber(r.var.ctype)] or cterr(r.var.ctype))
			fb.src:putf("vp = memoryview(vp, sizeofss(ss)*%d, %s)\n", ffi.sizeof(r.var.ctype), fmt)
		end
		if r.vector == Py.builtins.memoryview then
			fb.src:putf("setattr(result, %s, vp)\n", attr)
			fb.src:put("C.Py_DecRef(vp)\n")
		else
			fb.src:putf("vp%d = vp\n", i)
		end
		fb.src:put("end\n")
	end
	fb.src:put("jump(S, X)\n")
	for i,r in ipairs(roots) do
		fb.src:put("do\n")
		if r.havevec then
			if r.vector ~= Py.builtins.memoryview then
				local ctid = tonumber(r.var.ctype)
				local kind = Py.ctkind[ctid] or cterr(r.var.ctype)
				if r.havetype and r.constructor ~= Py.builtins[kind] then
					-- should be done in fhk_lang_Python aswell.
					error("TODO: vector convert.")
				end
				-- no need to decref: call1 eats the reference.
				fb.upv.call1 = Py.call1
				fb.src:putf("local x = ocheck(call1(%s, vp%d))\n", driver.upval(fb, r.vector), i)
			end
		else
			local ctid = tonumber(r.var.ctype)
			local ctp = driver.upval(fb, ffi.typeof("$*", r.var.ctype))
			fb.src:putf(
				"local x = ocheck(C.%s(cast(%s, vp%d)[0]))\n",
				Py.ctconvf[ctid] or cterr(r.var.ctype),
				ctp,
				i
			)
			local kind = Py.ctkind[ctid] or cterr(r.var.ctype)
			if r.constructor ~= Py.builtins[kind] then
				fb.upv.call1 = call1
				-- no need to decref: call1 eats the reference
				fb.src:putf("x = ocheck(call1(%s, x))\n", driver.upval(fb, r.constructor))
			end
		end
		if r.vector ~= Py.builtins.memoryview then
			local attr = driver.upval(fb, r.pyattr)
			fb.src:putf("setattr(result, %s, x)\n", attr)
			fb.src:put("C.Py_DecRef(x)\n")
		end
		fb.src:put("end\n")
	end
end

local function pyx_ready(fhk)
	local graph = rules.buildgraph(fhk.state)
	local jump = driver.jump(graph)
	local fb = driver.fbuf()
	for i,s in ipairs(fhk) do
		buildsolver(fb, s, jump)
		fhk[i] = driver.ffunc(graph, fb, "S, X, result, subsets")
		driver.reset(fb)
	end
	local init = rules.buildinit(fhk.state)
	local buf
	local G = driver.build(graph, function(size)
		buf = C.PyMem_Malloc(size)
		return buf
	end)
	ffi.gc(G, function() C.PyMem_Free(buf) end)
	return function(X, m)
		local S = ctypes.solver(G, ffi.cast("fhk_mem *", m))
		init(S, X)
		return S
	end
end

local function pyx_read(fhk, o)
	return rules.read(fhk.state, tostr(o))
end

local function errvisit()
	error("can't define a new model here")
end

local function pyx_model(fhk, name, decl, f)
	name = tostr(name)
	decl = tostr(decl)
	local def, err = load(string.format("return {%s}", decl))
	if not def then error(err) end
	f = ffi.cast("PyObject *", f)
	C.Py_IncRef(f)
	f = gcocheck(f)
	return rules.read(fhk.state, glib.model(name, glib.env(errvisit).read(def), glib.impl.Python(f)))
end

--------------------------------------------------------------------------------

return {
	new    = pyx_new,
	solver = pyx_solver,
	ready  = pyx_ready,
	read   = pyx_read,
	model  = pyx_model
}
