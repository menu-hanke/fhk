local fhk = require "fhk"
local buffer = require "string.buffer"

-- value doesn't matter, as long as it's something unique enough
local any = "any"

local function query_fails(query, msg)
	query.fail = msg or true
end

local query_mt = {
	__index = {
		fails = query_fails
	}
}

local function solution(ctx, values)
	local query, solution = {}, {}
	local i = 0
	for name, v in pairs(values) do
		local alias = string.format("var%d", i)
		table.insert(query, {name, alias=alias, value=fhk.intern()})
		solution[alias] = {
			values = type(v) == "table" and v or {v},
			var = name
		}
	end
	local q = setmetatable({
		query = ctx.graph:query(query),
		solution = solution
	}, query_mt)
	table.insert(ctx.queries, q)
	return q
end

local function checksolution(result, solution)
	local mismatch = {}
	for name, sol in pairs(solution) do
		local r = result[name]
		for i,x in ipairs(sol.values) do
			if x ~= any and x ~= r[i-1] then
				table.insert(mismatch, {var=sol.var, i=i-1, r=r[i-1], x=x})
			end
		end
	end
	if #mismatch > 0 then
		local buf = buffer.new()
		local prev
		buf:put("mismatched values:\n")
		for _,m in ipairs(mismatch) do
			if m.var ~= prev then
				buf:put("variable: ", m.var, "\n")
				buf:put(" i  |    got   | expected\n")
				buf:put("----+----------+----------\n")
				prev = m.var
			end
			buf:putf("%03d  %-10g %-10g\n", m.i, m.r, m.x)
		end
		error(tostring(buf))
	end
end

local function gtest(f)
	local graph = fhk.graph()
	local ctx = {graph=graph, queries={}}
	local env = graph:read()
	env.solution = function(...) return solution(ctx, ...) end
	env.any = any
	setfenv(f, env)()
	graph:prepare()
	for _,q in ipairs(ctx.queries) do
		if q.fail then
			local ok, e = pcall(q.query)
			if ok then error("query was supposed to fail, but didn't") end
			if type(q.fail) == "string" and not e:match(q.fail) then
				error(string.format("query failed with the wrong error: %s", e))
			end
		else
			local result = q.query()
			checksolution(result, q.solution)
		end
	end
end

return {
	g = function(f) return function() return gtest(f) end end
}
