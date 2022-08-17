local ctypes = require "fhk_ctypes"
local driver = require "fhk_driver"
local C = require "fhk_clib"
local ffi = require "ffi"
local buffer = require "string.buffer"

---- value/subset tag ----------------------------------------

-- (value) embed a scalar in the struct
local scalar = { tag="scalar" }

-- (value) embed a pointer to solver memory
local intern = { tag="intern" }

-- (value) `f` returns a cdata buffer to copy the value into
-- (subset) `f` returns a subset or index table
local function func(f)
	return { tag="func", f=f }
end

local function key(k)
	return func(function(X) return X[k] end)
end

-- (subset) use this map's value
local function map(var)
	return { tag="map", var=var }
end

---- queries ----------------------------------------

local function cname(name)
	return name:gsub("[^%w]", "_"):gsub("^([^%a_])", "_%1")
end

local function tovalue(x)
	if type(x) == "string" then return key(x) end
	return x
end

local function tosubset(x)
	if type(x) == "string" then return key(x) end
	if type(x) == "table" and x.handle then return map(x) end
	if type(x) == "function" then return func(x) end
	return x
end

local function query_setroots(graph, query, x, modifiers)
	if type(x) == "string" or (type(x) == "table" and x.handle) then
		local var = graph:getvar(x)
		local subset = modifiers.subset
		if not subset then
			subset = map(var.group)
		elseif subset.tag == "map" and type(subset.var) ~= "table" then
			subset = map(graph:getvar(subset.var))
		end
		table.insert(query, {
			var    = var,
			name   = modifiers.alias
				or (type(x) == "string" and cname(x))
				or (var.name and cname(var.name))
				or string.format("_%x", var.handle),
			value  = modifiers.value, -- maybe nil
			subset = subset
		})
	else
		modifiers = {
			alias = x.alias or modifiers.alias,
			value = tovalue(x.value) or modifiers.value,
			subset = tosubset(x.subset) or modifiers.subset
		}
		for _,r in ipairs(x) do
			query_setroots(graph, query, r, modifiers)
		end
	end
end

local function err_unbound()
	error("graph:prepare() not called")
end

local function graph_query(graph, ...)
	local query = {}
	table.insert(graph.queries, query)
	query_setroots(graph, query, {...}, {})
	query.trampoline = load([[
		local solve = ...
		return function(S, X)
			return solve(S, X)
		end
	]])(err_unbound)
	return query.trampoline
end

local function defaultvalue(v)
	if v.subset.tag == "map" and v.subset.var.mode == "s" then
		return scalar
	else
		return intern
	end
end

local function query_ctype(query)
	-- TODO: sort by size so the struct doesn't have holes
	local ctv = {}
	local buf = buffer.new()
	buf:put("struct {\n")
	for _,v in ipairs(query) do
		if not v.value then
			v.value = defaultvalue(v)
		end
		table.insert(ctv, v.var.ctype)
		buf:putf("$ %s%s;\n", v.value.tag == "scalar" and "" or "*", v.name)
		if v.value.tag == "intern" then
			query.anchor = true
		end
	end
	if query.anchor then
		buf:put("fhk_mem *__fhk_mem;\n")
	end
	buf:put("}")
	query.ctype = ffi.typeof(tostring(buf), unpack(ctv))
end

local function query_gcmem(result)
	C.fhk_destroy_mem(result.__fhk_mem)
end

local function query_solvefunc(graph, query, G)
	local code = driver.code()
	code.upv.C = C
	code.upv.G = G
	code.upv.J = graph.J
	code.src:put("local function solve(S, X, result)\n")
	local ss = {}
	for i,v in ipairs(query) do
		if v.subset.tag == "map" then
			code.src:putf("C.fhk_setrootM(S, %d, %d, 0)\n", v.var.idx, v.subset.var.idx)
		elseif v.subset.tag == "func" then
			if not ss[v.subset.f] then
				ss[v.subset.f] = string.format("ss%d", i)
				code.src:putf("local %s = %s(X)\n", ss[v.subset.f], code:upval(v.subset.f))
			end
			code.src:putf("C.fhk_setrootK(S, %d, %s)\n", v.var.idx, ss[v.subset.f])
		end
	end
	code.src:put("J[C.fhk_continue(S)](S, X)\n")
	for i,v in ipairs(query) do
		local subset
		if v.subset.tag == "map" then
			if not code.upv.subsetpp then
				code.upv.cast = ffi.cast
				code.upv.subsetpp = ffi.typeof("fhk_subset **")
			end
			if not ss[v.subset.var] then
				ss[v.subset.var] = string.format("ss%d", i)
				code.src:putf("local %s = cast(subsetpp, S+1)[%d][0]\n", ss[v.subset.var], v.subset.var.idx)
			end
			subset = ss[v.subset.var]
		elseif v.subset.tag == "func" then
			subset = ss[v.subset.f]
		end
		if v.value.tag == "scalar" then
			code.upv.cast = ffi.cast
			local ctpp = code:upval(ffi.typeof("$**", v.var.ctype))
			code.src:putf("result.%s = cast(%s, S+1)[%d][%s]\n", v.name, ctpp, v.var.idx, subset)
		elseif v.value.tag == "intern" then
			code.src:putf("result.%s = C.fhk_getvalueD(S, %d, %s)\n", v.name, v.var.idx, subset)
		elseif v.value.tag == "func" then
			code.src:putf([[
				result.%s = %s(X)
				C.fhk_getvalue(S, %d, %s, result.%s)
			]], v.name, code:upval(v.value.f),
			v.var.idx, subset, v.name)
		end
	end
	code.src:put("end\n")
	code.upv.istype = ffi.istype
	code.upv.solverp = ffi.typeof("fhk_solver *")
	code.upv.resultct = query.ctype
	code.src:put([[
		return function(S, X)
			if istype(solverp, S) then
				local result = resultct()
				solve(S, X, result)
				return result
			else
				X = S
				local mem = C.fhk_create_mem()
				S = C.fhk_create_solver(mem, G)
	]])
	if query.anchor then
		code.upv.resultp = ffi.typeof("$*", query.ctype)
		code.upv.gc = ffi.gc
		code.upv.query_gcmem = query_gcmem
		code.src:putf([[
				local result = cast(resultp, C.fhk_mem_alloc(mem, %d, %d))
				gc(result, query_gcmem).__fhk_mem = mem
		]], ffi.sizeof(query.ctype), ffi.alignof(query.ctype))
	else
		code.src:put([[
				local result = resultct()
		]])
	end
	code.src:put([[
				solve(S, X, result)
	]])
	if not query.anchor then
		code.src:put([[
				C.fhk_destroy_mem(mem)
		]])
	end
	code.src:put([[
				return result
			end
		end
	]])
	return code:emit()
end

local function query_prepare(graph, query, G)
	query_ctype(query)
	debug.setupvalue(query.trampoline, 1, query_solvefunc(graph, query, G))
end

local function malloc(size)
	ffi.cdef [[
		void *malloc(size_t);
		void free(void *);
	]]
	malloc = C.malloc
	return malloc(size)
end

local function graph_prepare(graph, alloc)
	graph:analyze()
	for _,q in ipairs(graph.queries) do
		for _,v in ipairs(q) do
			graph:mark(v.var)
		end
	end
	graph:layout()
	local size = graph:size()
	local buf = (alloc or malloc)(size)
	local G = graph:build(buf)
	if not alloc then
		ffi.gc(G, function() C.free(buf) end)
	end
	for _,q in ipairs(graph.queries) do
		query_prepare(graph, q, G)
	end
	return G
end

local function graph(...)
	local graph = driver.graph(...)
	graph.queries = {}
	graph.query = graph_query
	graph.prepare = graph_prepare
	return graph
end

---- var types ----------------------------------------

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
	return driver.virtual(function(var)
		if not var.name then return end
		local _, name = driver.splitname(var.name)
		local field = refct:member(name)
		if not field then return end
		driver.setcts(var, field.type)
		if type(source) == "cdata" then
			var.impl = driver.newimpl(driver.builtins.vrefk, {ptr=ffi.cast("uint8_t *", source) + field.offset})
		else
			var.impl = driver.newimpl(driver.builtins.vrefs, {f=source, offset=field.offset})
		end
	end)
end

-- array(cdata, subset)
-- array(ctype, function : inst -> ptr,subset)
local function array(a, b)
	return {
		driver.ctype(type(b) == "function" and a or require("reflect").typeof(a).element_type),
		type(b) == "function"
			and driver.impl(driver.builtins.vrefd, {f=b})
			or driver.impl(driver.builtins.vrefk, {ptr=a, ss=b})
	}
end

--------------------------------------------------------------------------------

return {
	scalar    = function() return scalar end,
	intern    = function() return intern end,
	func      = func,
	key       = key,
	map       = map,
	graph     = graph,
	struct    = struct,
	array     = array,

	-- ctypes
	emptyset  = ctypes.emptyset,
	space0    = ctypes.space0,
	space1    = ctypes.space1,
	interval0 = ctypes.interval0,
	interval1 = ctypes.interval1,
	tosubset  = ctypes.tosubset,
	mem       = ctypes.mem,
	solver    = ctypes.solver
}
