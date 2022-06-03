local ctypes = require "fhk_ctypes"
local driver = require "fhk_driver"
local lib = require "fhk_lib"
local ffi = require "ffi"

-- value doesn't matter as long as it's something unique
local na = "na"
local any = "any"

---- helpers ----------------------------------------

local function anchor(test, v)
	table.insert(test.anchor, v)
end

local function toname(name)
	return name:match("#") and name or ("default#"..name)
end

local function tofunc(f)
	if type(f) == "number" then return function() return f end end
	if type(f) == "cdata" then return function(i) return f[i] end end
	if type(f) == "table" then
		return function(i)
			i = i+1 -- 0->1 indexing
			if f[i] == na or not f[i] then
				error(string.format("trap na access: %d (%s)", i, f[i]))
			end
			return f[i]
		end
	end
	return f
end

local function tomapfunc(test, f)
	if type(f) == "table" then
		local a
		f, a = ctypes.tosubset(f)
		anchor(test, a)
	end
	if type(f) == "number" or type(f) == "cdata" then return function() return f end end
	return function(inst)
		local ss, a
		ss = f(inst)
		if type(ss) == "table" then
			ss, a = ctypes.tosubset(ss)
			anchor(test, a)
		end
		return ss
	end
end

local function checksyntax(src, x, ...)
	if not x then
		error(string.format("syntax error -> %s", src))
	else
		return x, ...
	end
end

---- declarations ----------------------------------------

local function declgroup(test, decl)
	local name = (type(decl) == "string" and decl) or decl.name or decl[1]
	local group = test.groups[name]
	if not group then
		group = { obj = driver.addgroup(test.graph, name) }
		test.groups[name] = group
	end
	if type(decl) == "table" then
		group.shape = decl.shape or group.shape
	end
	return group
end

local function declvar(test, decl)
	local name = toname(type(decl) == "string" and decl or (decl[1] or decl.name))
	local var = test.vars[name]
	if not var then
		local group = declgroup(test, lib.groupof(name))
		var = { obj = driver.addvar(test.graph, group.obj, name), needctype=true }
		test.vars[name] = var
	end
	if type(decl) == "table" and decl.ctype then
		driver.setctype(var.obj, decl.ctype)
		var.needctype = false
	end
	return var
end

local function declmap(test, flags, value)
	local map = { obj = driver.addmap(test.graph, flags), flags=flags, value=value }
	table.insert(test.maps, map)
	return map
end

local function declmap2(test, decl)
	local name = decl.name or decl[1]
	test.map2s[name] = driver.umap2(decl.forward.obj, decl.inverse.obj)
end

local function getmap2(test, name)
	if name == "ident" then return driver.ident end
	if name == "space" then return driver.space end
	return test.map2s[name] or error(string.format("undefined map2: %s", name))
end

local function checkarg(op, arg)
	if op == "&" or op == "!&" then
		local out = {}
		for v in arg:gmatch("[^,]+") do
			table.insert(out, tonumber(v) or error(string.format("expected number: %s", v)))
		end
		return out
	end
	return arg
end

local function declguard(test, decl)
	local var, op, arg = checksyntax(decl, decl:match("^([%w#_%-]+)([><&!]=?)(.+)$"))
	var = declvar(test, var)
	return driver.addguard(test.graph, var.obj, decl, op, checkarg(op, arg))
end

local function iteredges(decl)
	-- name, map
	return decl:gmatch("([^,:]+):?([^,]*)")
end

local function declmodel(test, decl)
	local signature = decl[1]:gsub("%s", "")
	local params, returns = checksyntax(
		signature,
		signature:gsub("^[^#]+#", ""):match("([%w#_%-:@,]*)%->([%w#_%-:@,]*)")
	)

	local name = toname(decl.name or decl[1])
	local groupname = lib.groupof(name)
	local group = declgroup(test, groupname)
	local model = {
		obj = driver.addmodel(
			test.graph,
			group.obj,
			decl.k or 0,
			decl.c or 1,
			name
		),
		value = decl.f or decl[2]
	}
	test.models[name] = model

	for name,map in iteredges(params) do
		name = toname(name)
		if map == "" and lib.groupof(name) == groupname then map = "ident" end
		map = getmap2(test, map)
		driver.addparam(test.graph, model.obj, declvar(test, name).obj, map)
	end

	for name,map in iteredges(returns) do
		name = toname(name)
		if map == "" and lib.groupof(name) == groupname then map = "ident" end
		map = getmap2(test, map)
		driver.addreturn(test.graph, model.obj, declvar(test, name).obj, map)
	end

	for c in signature:gmatch("%[(.-)%]") do
		local guard, map, penalty = checksyntax(c, c:match("^([^:%+]+):?([^%+]*)%+?([einf%d%.]*)$"))
		if map == "" and lib.groupof(toname(guard)) == groupname then map = "ident" end
		map = getmap2(test, map)
		local g = declguard(test, guard)
		driver.addcheck(test.graph, model.obj, g, map, tonumber(penalty))
	end
end

local function setpinned(test, decl)
	if type(decl) == "table" then
		for _,x in ipairs(decl) do
			setpinned(test, x)
		end
	elseif type(decl) == "string" then
		driver.pin(test.graph, declvar(test, decl).obj)
	end
end

local function shapehint(test, decl)
	for name, values in pairs(decl) do
		if type(values) == "table" then
			local groupname = lib.groupof(toname(name))
			local group = declgroup(test, groupname)
			local oldnum = group.shape
			local num = #values
			if oldnum and num ~= oldnum then
				error(string.format("conflicting group shape: %s: %d ~= %d", groupname, oldnum, num))
			end
			group.shape = num
		end
	end
end

local function setgiven(test, decl)
	for name,value in pairs(decl) do
		declvar(test, name).value = value
	end
end

local function setroots(test, decl)
	for name,value in pairs(decl) do
		setpinned(test, name)
		table.insert(test.roots, {name=name, obj=declvar(test, name).obj, value=value})
	end
end

---- actions ----------------------------------------

local function typing(test)
	for _,v in pairs(test.vars) do
		if v.needctype then
			driver.setctype(v.obj, "double")
		end
	end
end

local function compile(test)
	local fb = driver.fbuf()
	for name,v in pairs(test.vars) do
		if v.value then
			driver.vrefv(fb, { var = v.obj, f = tofunc(v.value) })
		else
			driver.trap(fb, { mes = string.format("access var: %s", name) })
		end
		driver.jfunc(test.graph, v.obj, fb)
		driver.reset(fb)
	end
	local luamod = driver.loadlang(test.graph, "Lua")
	for name,m in pairs(test.models) do
		if m.value then
			luamod(fb, m.obj, tofunc(m.value))
		else
			driver.trap(fb, { mes = string.format("access model: %s", name) })
		end
		driver.jfunc(test.graph, m.obj, fb)
		driver.reset(fb)
	end
	for _,m in ipairs(test.maps) do
		-- unreferenced maps will be skipped even without explicit pruning.
		if m.obj.idx then
			if m.value then
				driver.mapcallf(fb, { map = m.obj, f = tomapfunc(test, m.value) })
			else
				driver.trap(fb, { mes = string.format("access map [%d]", m.obj.idx)})
			end
			driver.jfunc(test.graph, m.obj, fb)
			driver.reset(fb)
		end
	end
end

local function build(test)
	typing(test)
	driver.layout(test.graph)
	compile(test)
	driver.jtab(test.graph)
	test.jump = driver.jump(test.graph)
	test.G = driver.build(test.graph)
end

local function checksolution(test)
	local S = ctypes.solver(test.G)
	for _,g in pairs(test.groups) do
		if g.shape then
			S:setshape(g.obj.idx, g.shape)
		end
	end
	for _,r in ipairs(test.roots) do
		local idx = {}
		for i,v in ipairs(r.value) do
			if v ~= na then
				table.insert(idx, i-1)
			end
		end
		local ss, a = ctypes.tosubset(idx)
		anchor(test, a)
		r.ptr = ffi.cast(ffi.typeof("$*", r.obj.ctype), S:setrootD(r.obj.idx, ss))
	end
	test.jump(S)
	for _,r in ipairs(test.roots) do
		local idx = 0
		for i,v in ipairs(r.value) do
			if v ~= na then
				if v ~= any and r.ptr[idx] ~= v then
					error(string.format("wrong result %s:%d -- expected: %s, got: %s",
						r.name, i-1, v, r.ptr[idx]))
				end
				idx = idx+1
			end
		end
	end
end

local function checkprune(test, prune)
	typing(test)
	driver.prune(test.graph)
	driver.layout(test.graph)
	local lookup = {}
	for _,name in ipairs(prune) do lookup[toname(name)] = true end
	for _,tab in ipairs({test.vars, test.models}) do
		for name,x in pairs(tab) do
			if lookup[name] and not x.obj.idx then
				error(string.format("'%s' was pruned", name))
			end
			if x.obj.idx and not lookup[name] then
				error(string.format("'%s' was not pruned", name))
			end
		end
	end
end

---- test state ----------------------------------------

local function jump_err()
	error("jump function not compiled")
end

local function newtest()
	return {
		graph  = driver.graph(),
		groups = {},  --> [group name] => {obj=driver group, shape=?}
		vars   = {},  --> [var name] => {obj=driver var, value=?}
		models = {},  --> [model name] => {obj=driver model, value=?}
		guards = {},  --> [guard name] => {obj=driver guard}
		maps   = {},  --> [ {obj=driver map, value=?} ]
		map2s  = {},  --> [map name] => {obj=driver map2}
		roots  = {},  --> [ {name, value} ]
		anchor = {},  --> [ ... ]
		jump   = jump_err
	}
end

local function inject(env)
	local test = newtest()

	env.na = na
	env.any = any

	function env.group(decl)        declgroup(test, decl) end
	function env.var(decl)          declvar(test, decl) end
	function env.model(decl)        declmodel(test, decl) end
	function env.guard(decl)        declguard(test, decl) end
	function env.map(flags, func)   return declmap(test, flags, func) end
	function env.map2(decl)         declmap2(test, decl) end
	function env.pin(decl)          setpinned(test, decl) end

	function env.given(decl)
		shapehint(test, decl)
		setgiven(test, decl)
	end

	function env.solution(decl)
		shapehint(test, decl)
		setroots(test, decl)
		build(test)
		checksolution(test)
	end

	function env.pruned(decl)
		checkprune(test, decl)
	end

	return env
end

return function(f)
	return setfenv(f, inject(setmetatable({}, {__index=_G})))
end
