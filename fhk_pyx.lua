local driver = require "fhk_driver"
local C = require "fhk_clib"
local ffi = require "ffi"
local cast = ffi.cast
local Py = require "fhk_lang_Python"
local pyC, gcocheckref = Py.C, Py.gcocheckref
local PyObjectp, solverp = ffi.typeof("PyObject *"), ffi.typeof("fhk_solver *")

ffi.cdef[[
void *PyMem_Malloc(size_t);
void fhk_pyx_setrootinfo(void *, void *, int);
int fhk_pyx_setvalue_scatter_space(fhk_solver *, int, void *, void *);
int fhk_pyx_setvalue_scatter2(fhk_solver *, int, void *, void *);
]]

local function PyObject(x)
	return cast(PyObjectp, x)
end

local function pyx_graph_ldef(graph, src)
	assert(load(src, "=(fhk:ldef)", nil, graph:read()))()
end

local function pyx_graph_setroot(graph, obj, var)
	table.insert(graph.roots, { var = graph:getvar(var), obj = gcocheckref(PyObject(obj)) })
end

local function vrefvpy(J, o)
	local code = driver.code()
	code.upv.pyC = pyC
	code.upv.f = o.impl.f
	code.upv.ocheck = Py.ocheck
	code.upv.echeck3 = Py.echeck3
	if #o.impl.params > 0 then
		code.upv.args = Py.tuple(#o.impl.params)
		for i=1, #o.impl.params do
			local p = o.impl.params:sub(i,i)
			if p == "i" then
				code.src:putf("pyC.PyTuple_SetItem(args, %d, ocheck(pyC.PyLong_FromSsize_t(S.inst)))\n", i-1)
			elseif p == "x" then
				code.src:putf([[
					pyC.Py_IncRef(X)
					pyC.PyTuple_SetItem(args, %d, X)
				]], i-1)
			end
		end
		code.src:put("local r = ocheck(pyC.PyObject_Call(f, args, nil))\n")
	else
		code.src:put("local r = ocheck(pyC.PyObject_CallNoArgs(f))\n")
	end
	if pyC.Py_IsNone(o.impl.vec) == 0 then
		-- TODO: use fhk_setvalue/fhk_setvalueC for directly copyable vectors
		code.src:putf(
			[[
				local ok = C.%s(S, %d, %s, r)
				if ok == -1 then echeck3(r) end
			]],
			o.impl.ss and "fhk_pyx_setvalue_scatter2" or "fhk_pyx_setvalue_scatter_space",
			o.idx, code:upval(Py.memfmt(o.ctype))
		)
	else
		code.upv.cast = ffi.cast
		code.src:putf([[	
			local v = pyC.%s(r)
			cast(%s, C.fhk_setvalueD(S, %d, S.inst))[0] = v
			pyC.Py_DecRef(r)
			if v == -1 then echeck3(r) end
		]], Py.pycconvf(o.ctype), code:upval(ffi.typeof("$*", o.ctype)), o.idx)
	end
	code.name = string.format("=fhk:vrefvpy<%s>@%s", driver.desc(o), o.impl.desc)
	return code:emitjmp(J)
end

local builtins = { int = driver.int, float = driver.fp, bool = "bool" }
local function pyx_graph_given(graph, var, f, params, vec, cls, ss, desc, ldef)
	var = graph:getvar(var)
	cls = PyObject(cls)
	for name, obj in pairs(Py.builtins) do
		if cls == obj then
			if builtins[name] then
				driver.setcts(var, builtins[name])
				break
			end
		end
	end
	var.impl = driver.newimpl(vrefvpy, {
		f      = gcocheckref(PyObject(f)),
		vec    = gcocheckref(PyObject(vec)),
		ss     = ss,
		params = params,
		desc   = desc
	})
	if ldef then
		local env = graph:read()
		env.var(var)(assert(load("return "..ldef, "=(fhk:given.ldef)", nil, env)()))
	end
end

local function pyx_graph_model(graph, f, name, ldef)
	local env = graph:read()
	env.model(name) {
		driver.impl("Python", gcocheckref(PyObject(f))),
		ldef and {assert(load("return "..ldef, "=(fhk:model.ldef)", nil, env))()}
	}
end

local function pyx_graph_prepare(graph)
	graph:analyze()
	for _,r in ipairs(graph.roots) do
		graph:mark(r.var)
	end
	graph:layout()
	for _,r in ipairs(graph.roots) do
		C.fhk_pyx_setrootinfo(r.obj, Py.memfmt(r.var.ctype), r.var.idx)
	end
	local size = graph:size()
	-- note: match deallocation in fhk_api.pyx
	local buf = pyC.PyMem_Malloc(size)
	return tonumber(ffi.cast("intptr_t", buf)), tonumber(ffi.cast("intptr_t", graph:build(buf)))
end

local function pyxrt_continuefunc(J)
	return function(S, X)
		S = cast(solverp, S)
		X = PyObject(X)
		return J[C.fhk_continue(S)](S, X)
	end
end

local function pyx_graph()
	local graph = driver.graph()
	graph.roots = {}
	graph.ldef = pyx_graph_ldef
	graph.setroot = pyx_graph_setroot
	graph.given = pyx_graph_given
	graph.model = pyx_graph_model
	graph.prepare = pyx_graph_prepare
	return graph, pyxrt_continuefunc(graph.J)
end

return {
	graph = pyx_graph
}
