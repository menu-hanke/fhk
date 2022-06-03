local ctypes = require "fhk_ctypes"
local driver = require "fhk_driver"
local rules = require "fhk_rules"
local lib = require "fhk_lib"
local C = require "fhk_clib"
local buffer = require "string.buffer"
local ffi = require "ffi"

---- roots & solvers ----------------------------------------

-- value: `value` is a cdata pointer to the buffer.
-- subset: `value` is a number/cdata -> subset constant
--                      table -> `value` is converted to subset and anchored to the ctype.
local function fixed(value)
	return {
		tag   = "fixed",
		value = value
	}
end

-- value: `f` will return a cdata pointer to the buffer.
-- subset: `f` will return a number/cdata/table subset. tables are converted.
local function func(f)
	return {
		tag  = "func",
		f    = f
	}
end

-- value/subset: read key from parameter table/cdata.
local function key(name)
	return func(function(X) return X[name] end)
end

-- subset: use space of `group`
local function space(group)
	return {
		tag   = "space",
		group = group
	}
end

-- value: alloc(size,align) => void *
--        the difference to `func` is that this function is a generic allocator, while `func`
--        operates on the X parameter.
local function alloc(allocator)
	return {
		tag       = "alloc",
		allocator = allocator
	}
end

-- value: return a pointer to solver memory.
local intern = { tag = "intern" }

-- value: embed scalar in ctype.
local scalar = { tag = "scalar" }

-- value: embed vector in ctype.
local function vector(n)
	return {
		tag = "vector",
		n   = n
	}
end

local function tosubset(x)
	if type(x) == "string" then return key(x) end
	if type(x) == "number" or type(x) == "cdata" then return fixed(x) end
	-- TODO: the constant subset case below should be computed once and anchored
	-- to the result ctype.
	if type(x) == "table" and not x.tag then return func(function() return x end) end
	if type(x) == "function" then return func(x) end
	return x
end

local function tovalue(x)
	if type(x) == "string" then return key(x) end
	if type(x) == "cdata" then return fixed(x) end
	if type(x) == "function" then return func(x) end
	return x
end

local function cname(name)
	return name:gsub("[^%w]", "_"):gsub("^([^%a_])", "_%1")
end

local function isanchored(solver)
	for _,r in ipairs(solver) do
		if r.value.tag == "intern" then
			return true
		end
	end
	return false
end

local function initsolver_template()
	return load([[
		local C, G, init, solverctp, arenactp, istype
		return function(S, X)
			if istype(solverctp, S) then
				init(S, X)
			else
				local A
				if istype(arenactp, S) then
					A = S
				else
					X = S
					A = C.fhk_create_arena(2^17)
				end
				S = C.fhk_create_solver(G, A)
				init(S, X)
				return S, A
			end
		end
	]], "=fhk:init")()
end

local function solver_template(solver, chunkname)
	local anchored = isanchored(solver)
	local src = buffer.new()
	src:put([[
		local C, G, rct, rctp, solverctp, initsolver, jump, istype, cast, sizeof, alignof
		return function(S, X)
			if istype(solverctp, S) then
				local R = rct()
				R['fhk$init'](R, S, X)
				jump(S, X)
				return R
			else
				X = S
				local S, A = initsolver(X)
	]])
	if anchored then
		src:put([[
				local R = cast(rctp, C.fhk_alloc(A, sizeof(rct), alignof(rct)))
				R.__fhk_arena = A
		]])
	else
		src:put([[
				local R = rct()
		]])
	end
	src:put([[
				R['fhk$init'](R, S, X)
				jump(S, X)
	]])
	if not anchored then
		src:put([[
				C.fhk_destroy_arena(A)
		]])
	end
	src:put([[
				return R
			end
		end
	]])
	return load(src, chunkname)()
end

local function setroots(fhk, solver, names, x, modifiers)
	if type(x) == "string" then
		table.insert(names, x)
		local subset = modifiers.subset
		if (not subset) or (subset.tag == "space" and not subset.group) then
			subset = space(rules.getgroup(fhk.state, lib.groupof(x)))
		elseif subset.tag == "space" then
			subset = space(rules.getgroup(subset.group))
		end
		table.insert(solver, {
			var    = rules.root(fhk.state, x),
			name   = modifiers.alias or cname(x),
			value  = modifiers.value or intern,
			subset = subset
		})
	else
		modifiers = {
			alias  = x.alias or modifiers.alias,
			value  = tovalue(x.value) or modifiers.value,
			subset = tosubset(x.subset) or modifiers.subset
		}
		for _,r in ipairs(x) do
			setroots(fhk, solver, names, r, modifiers)
		end
	end
end

local function fhk_solver(fhk, ...)
	local solver = {}
	local names = {}
	setroots(fhk, solver, {}, {...}, {})
	table.insert(fhk.solvers, solver)
	solver.desc = table.concat(names, ",")
	solver.template = solver_template(solver, string.format("=fhk:solver-%s", solver.desc))
	return solver.template
end

local function fhk_graph(fhk, ...)
	rules.read(fhk.state, ...)
	return fhk
end

local function cmp(a, b) return a == b and "=" or (a < b and "<" or ">") end
local function addrof(x) return string.format("%p", x) end

local function sscmp(a, b)
	if a.tag ~= b.tag then return cmp(a.tag, b.tag) end
	if a.tag == "fixed" then return cmp(addrof(a.value), addrof(b.value)) end
	if a.tag == "func" then return cmp(addrof(a.f), addrof(b.f)) end
	if a.tag == "space" then return cmp(a.group.idx, b.group.idx) end
	assert(false)
end

local function rctinit(solver, rct)
	table.sort(solver, function(a, b) return sscmp(a.subset, b.subset) == "<" end)
	local upv = {}
	local buf = buffer.new()
	local subset
	for i,v in ipairs(solver) do
		if subset == nil or sscmp(subset, v.subset) ~= "=" then
			subset = v.subset
			local neednum = false
			for j=i, #solver do
				if sscmp(subset, solver[j].subset) ~= "=" then
					break
				end
				if solver[j].value.tag == "alloc" then
					neednum = true
					break
				end
			end
			if subset.tag == "fixed" then
				error("TODO")
			elseif subset.tag == "func" then
				local f = string.format("_f_%p", subset.f)
				upv[f] = subset.f
				upv.type = type
				upv.tosubset = ctypes.tosubset
				upv.arenaof = ctypes.arenaof
				if neednum then buf:put("local num\n") end
				buf:putf("local subset = %s(X)\n", f)
				buf:put("if type(subset) == 'table' then\n")
				if neednum then buf:put("num = #subset\n") end
				buf:put("subset = tosubset(subset, arenaof(S))\n")
				if neednum then
					upv.sizeofss = ctypes.sizeof
					buf:put("else num = sizeofss(subset)\n")
				end
				buf:put("end\n")
			elseif subset.tag == "space" then
				upv.mapstateK = ctypes.mapstateK
				buf:putf("local subset = mapstateK(S, %d)\n", subset.group.idx)
				if neednum then
					upv.sizeofss = ctypes.sizeof
					buf:put("local num = sizeofss(subset)\n")
				end
			end
		end
		local value = v.value
		if value.tag == "func" then
			local f = string.format("_f_%p", value.f)
			upv[f] = value.f
			buf:putf("R.%s = %s(X)\n", v.name, f)
		elseif value.tag == "alloc" then
			local f = string.format("_f_%p", value.allocator)
			upv[f] = value.allocator
			buf:putf("R.%s = %s(num*%d, %d)\n", f, ffi.sizeof(v.var.ctype), ffi.alignof(v.var.ctype))
		end
		if value.tag == "fixed" or value.tag == "func" or value.tag == "alloc" then
			buf:putf("C.fhk_setrootC(S, %d, subset, R.%s)\n", v.var.idx, v.name)
		elseif value.tag == "intern" then
			buf:putf("R.%s = C.fhk_setrootD(S, %d, subset)\n", v.name, v.var.idx)
		elseif value.tag == "scalar" or value.tag == "vector" then
			upv.cast = ffi.cast
			buf:putf(
				"C.fhk_setrootC(S, %d, subset, cast('uint8_t *', R)+%d)\n",
				v.var.idx,
				ffi.offsetof(rct, v.name)
			)
		end
	end
	local out = buffer.new()
	out:put("local C")
	local uval = {}
	for name, val in pairs(upv) do
		out:put(", ", name)
		table.insert(uval, val)
	end
	out:put(" = ...\n")
	out:put("return function(R, S, X)\n")
	out:put(buf)
	out:put("end")
	return load(out, string.format("=fhk:init-%s", solver.desc))(C, unpack(uval))
end

local function rct_gcarena(result)
	if result.__fhk_arena ~= nil then
		C.fhk_destroy_arena(result.__fhk_arena)
	end
end

local function rctype(solver)
	-- TODO: sort by size so the struct doesn't have holes
	local meta = { __index = {} }
	local ctv = {}
	local buf = buffer.new()
	buf:put("struct {\n")
	for _,v in ipairs(solver) do
		local value = v.value
		local subset = v.subset
		if value.tag == "fixed" then
			meta.__index[v.name] = value.value
		else
			table.insert(ctv, v.var.ctype)
			if value.tag == "func" or value.tag == "alloc" or value.tag == "intern" then
				buf:putf("$ *%s;\n", v.name)
			elseif value.tag == "scalar" then
				buf:putf("$ %s;\n", v.name)
			elseif value.tag == "vector" then
				buf:putf("$ %s[%d];\n", v.name, value.n)
			end
		end
		if subset.tag == "fixed" and type(subset.value) == "table" then
			error("TODO: anchor it to meta.__index")
		end
	end
	if isanchored(solver) then
		buf:put("fhk_arena *__fhk_arena;\n")
		meta.__gc = rct_gcarena
	end
	buf:put("}")
	local rct = ffi.typeof(tostring(buf), unpack(ctv))
	meta.__index["fhk$init"] = rctinit(solver, rct)
	return ffi.metatype(rct, meta)
end

local function setupvalues(f, upv)
	local i = 1
	while true do
		local name = debug.getupvalue(f, i)
		if name == nil then
			return
		end
		if upv[name] ~= nil then
			debug.setupvalue(f, i, upv[name])
		end
		i = i+1
	end
end

local function fhk_ready(fhk, alloc)
	local graph = rules.buildgraph(fhk.state)
	local G = driver.build(graph, alloc)
	local jump = driver.jump(graph)
	local solverctp = ffi.typeof("fhk_solver *")
	local arenactp = ffi.typeof("fhk_arena *")
	setupvalues(fhk.init, {
		C         = C,
		G         = G,
		init      = rules.buildinit(fhk.state),
		solverctp = solverctp,
		arenactp  = arenactp,
		istype    = ffi.istype
	})
	for _,s in ipairs(fhk.solvers) do
		local rct = rctype(s)
		setupvalues(s.template, {
			C          = C,
			G          = G,
			rct        = rct,
			rctp       = ffi.typeof("$*", rct),
			solverctp  = solverctp,
			initsolver = fhk.init,
			jump       = jump,
			istype     = ffi.istype,
			cast       = ffi.cast,
			sizeof     = ffi.sizeof,
			alignof    = ffi.alignof
		})
	end
end

---- fhk table ----------------------------------------

local fhk_mt = {
	__index = {
		graph = fhk_graph,
		ready = fhk_ready
	},
	__call = fhk_solver
}

local function new(...)
	return setmetatable({
		state   = rules.newstate(rules.composite({...})),
		init    = initsolver_template(),
		solvers = {}
	}, fhk_mt)
end

---- rules ----------------------------------------

-- struct(cdata)
-- struct(ctype, function)
local function struct(ctype, source)
	if not source then
		ctype, source = ffi.typeof(ctype), ctype
	end
	local refct = require("reflect").typeof(ctype)
	if refct.what == "ptr" then
		refct = refct.element_type
	end
	return rules.tagged("var", function(_, event)
		local field = refct:member(lib.ungroup(event.name))
		if not field then return end
		event.setcts(field.type)
		event.setjfunc(function(fb, var)
			if type(source) == "cdata" then
				driver.vrefk(fb, {ptr=ffi.cast("uint8_t *", source) + field.offset, var=var})
			else
				driver.vrefs(fb, {f=source, offset=field.offset, var=var})
			end
		end)
	end)
end

-- array(cdata, subset)
-- array(ctype, function : inst -> ptr,subset)
local function array(a, b)
	local ctype = type(b) == "function" and a or require("reflect").typeof(a).element_type
	return rules.tagged("var", function(_, event)
		event.setcts(ctype)
		event.setjfunc(function(fb, var)
			if type(b) == "function" then
				driver.vrefd(fb, {f=b, var=var})
			else
				driver.vrefk(fb, {ptr=a, var=var, ss=b})
			end
		end)
	end)
end

--------------------------------------------------------------------------------

return {
	new       = new,

	-- solver declarations
	fixed     = fixed,
	func      = func,
	key       = key,
	space     = space,
	alloc     = alloc,
	intern    = function() return intern end,
	scalar    = function() return scalar end,
	vector    = vector,

	-- view rules
	struct    = struct,
	array     = array,
	composite = rules.composite,
	group     = rules.group,
	tagged    = rules.tagged,
	named     = rules.named,
	virtual   = rules.virtual,
	shape     = rules.shape,
	shapeof   = rules.shapeof,
	edgerule  = rules.edgerule,
	map       = rules.map,
	label     = rules.label,

	-- utils
	groupof   = lib.groupof,
	ungroup   = lib.ungroup,

	-- re-exports
	c         = ctypes,
	g         = require "fhk_g"
}
