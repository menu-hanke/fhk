local ffi = require "ffi"
local driver = require "fhk_driver"
local rules = require "fhk_rules"
local C = require "fhk_clib"
local cast = ffi.cast

-- keep in sync with fhk.pyx!
ffi.cdef [[
	void fhk_py_gc(intptr_t);
	int fhk_py_shape(intptr_t, intptr_t);
	double fhk_py_vref_scalar_fp(intptr_t, void *, int);
	int64_t fhk_py_vref_scalar_int(intptr_t, void *, int);
	void fhk_py_vref_vector(fhk_solver *, int, intptr_t, void *, int, int32_t);
	fhk_subset fhk_py_getmapK(intptr_t, void *);
	fhk_subset fhk_py_getmapI(intptr_t, void *, int);

	void *PyMem_RawMalloc(size_t);
]]

---- python<->lua helpers  ----------------------------------------

local ref_ct = ffi.metatype([[
	struct {
		intptr_t ptr;
	}
]], { __gc = C.fhk_py_gc })

local py_reftab = setmetatable({}, {__mode="v"})

local function ispyptr(p)
	return ffi.istype(ref_ct, p)
end

local function addref(p)
	if py_reftab[p] then
		return py_reftab[p], false
	else
		py_reftab[p] = ref_ct(ffi.cast("intptr_t", p))
		return py_reftab[p], true
	end
end

local function call(f, ...)
	return xpcall(f, debug.traceback, ...)
end

---- rules & jfuncs ----------------------------------------

local function pyshapef(pf)
	return load([[
		local C, pf = ...
		return function(X)
			return (C.fhk_py_shape(pf, X.ptr))
		end
	]])(C, pf)
end

local function shape(x)
	if ispyptr(x) then
		x = pyshapef(x)
	end
	return rules.shape(x)
end

local function cttab(kv)
	local ret = {}
	for k,v in pairs(kv) do ret[tonumber(ffi.typeof(k))] = v end
	return ret
end

-- ctype -> python struct notation
-- see: https://docs.python.org/3/library/struct.html
local pyfmt = cttab {
	int8_t   = "b",
	uint8_t  = "B",
	bool     = "?",
	int16_t  = "h",
	uint16_t = "H",
	int32_t  = "i",
	uint32_t = "I",
	int64_t  = "q",
	uint64_t = "Q",
	float    = "f",
	double   = "d"
}

local function vrefpyvector(fb, var, pf, copy)
	local fmt = pyfmt[tonumber(var.ctype)]
		or error(string.format("ctype not supported by python struct module: %s", var.ctype))
	local flags = fmt:byte()
	if copy then flags = flags + 0x80000000 end
	fb.upv.pf = pf
	fb.src:putf(
		"C.fhk_py_vref_vector(S, %d, pf.ptr, X, S.inst, %d)\n",
		var.idx, bit.tobit(flags)
	)
	fb.name = string.format("=fhk:vrefpyvec<%s>@0x%x", var.name, pf.ptr)
end

local ctkind = cttab {
	float   = "fp",  double   = "fp",
	int8_t  = "int", uint8_t  = "int",
	int16_t = "int", uint16_t = "int",
	int32_t = "int", uint32_t = "int",
	int64_t = "int", uint64_t = "int"
}

local function vrefpyscalar(fb, var, pf)
	local what = ctkind[tonumber(var.ctype)] or error(string.format("ctype is not scalar: %s", var.ctype))
	fb.upv.pf = pf
	fb.upv.cast = ffi.cast
	fb.upv.ctp = ffi.typeof("$*", var.ctype)
	fb.src:putf(
		"cast(ctp, C.fhk_setvalueD(S, %d, S.inst))[0] = %s(pf.ptr, X, S.inst)\n",
		var.idx,
		what == "fp" and "C.fhk_py_vref_scalar_fp" or "C.fhk_py_vref_scalar_int"
	)
	fb.name = string.format("=fhk:vrefpy<%s>@0x%x", var.name, pf.ptr)
end

local function mapcallpy(fb, map, pf)
	fb.upv.pf = pf
	if map.flags:match("i") then
		fb.src:putf("C.fhk_setmapI(S, %d, S.inst, C.fhk_py_getmapI(pf.ptr, X, S.inst))\n", map.idx)
	else
		fb.src:putf("C.fhk_setmapK(S, %d, C.fhk_py_getmapK(pf.ptr, X))\n", map.idx)
	end
	fb.name = string.format("=fhk:mapcallpy(%s)<%s>@0x%x", map.flags, map.name, pf.ptr)
end

local function pyvirt(name, pf, sig)
	local copy, ctype, vec = sig:match("(!?)([%w_]*)(%]?)")
	return rules.tagged("var", rules.named(name, function(_, event)
		event.setjfunc(function(fb, var)
			if vec ~= "" then
				vrefpyvector(fb, var, pf, copy == "!")
			else
				vrefpyscalar(fb, var, pf)
			end
		end)
		if ctype ~= "" then
			event.setcts(ctype)
		end
	end))
end

local function pymap(name, inverse, flags, pf)
	return rules.tagged("map", rules.named(name, function(_, event)
		event.setinverse(inverse)
		event.setflags(flags)
		event.setjfunc(function(fb, map)
			mapcallpy(fb, map, pf)
		end)
	end))
end

---- roots & solvers ----------------------------------------

local function setroot(state, var, cts)
	rules.typehint(state, var, cts)
	return rules.root(state, var)
end

local function getroot(var)
	local idx = var.idx or error(string.format("var pruned or graph not layouted (%s)", var.name))
	local fmt = pyfmt[tonumber(var.ctype)] or error(string.format("unrepresentable ctype: %s", var.ctype))
	return idx, fmt
end

local function convjump(jump)
	return function(S, X)
		return jump(cast("fhk_solver *", S), X)
	end
end

local function ready(state, G)
	local graph = rules.buildgraph(state)
	local jump = convjump(driver.jump(graph))
	local init = rules.buildinit(state)
	G = ffi.cast("fhk_graph **", G)
	G[0] = driver.build(graph, function(size) return C.PyMem_RawMalloc(size) end)
	return init, jump
end

--------------------------------------------------------------------------------

return {
	rules   = rules,
	addref  = addref,
	call    = call,
	shape   = shape,
	pyvirt  = pyvirt,
	pymap   = pymap,
	setroot = setroot,
	getroot = getroot,
	ready   = ready
}
