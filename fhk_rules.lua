local driver = require "fhk_driver"
local glib = require "fhk_g"
local lib = require "fhk_lib"
local buffer = require "string.buffer"

--------------------------------------------------------------------------------
-- rules:
--     group       name                        setshape
--     var         name                        setcts         setjfunc
--     model       name                        setjfunc
--     guard       name                        setvar         setop        setargs
--     map         name                        setinverse     setjfunc     setflags
--     edge        model        var            setmap         setcts       setrank
--     label       name                        setvalue
--     emit.pre    name         obj      fb
--     emit.post   name         obj      fb
--------------------------------------------------------------------------------

local function newstate(rules, defaults)
	return {
		graph  = driver.graph(),
		rules  = rules,
		k      = (defaults and defaults.k) or 1,
		c      = (defaults and defaults.c) or 1.1,
		groups = {},  --> [group name] => {obj=driver group, shape=function()?}
		vars   = {},  --> [var name] => {obj=driver var, jfunc=function(fb)?, computed=bool}
		models = {},  --> [model name] => {obj=driver model, lang=string, args=?, skip=bool}
		guards = {},  --> [q|g: guard name] => driver guard
		maps   = {},  --> [map name] => {obj=driver map, map2=driver map2, jfunc=function(fb)?}
		labels = {},  --> [label name] => value
	}
end

local function checkp(ok, x, fmt, ...)
	if not ok then
		error(string.format("%s (in "..fmt..")", x, ...), 2)
	end
	return x
end

---- rule querying ----------------------------------------

local collect_mt = {
	__call = function(self, value)
		if self.value ~= nil and self.value ~= value then
			error(string.format("inconsistent value: %s ~= %s", self.value, value))
		end
		self.value = value
	end
}

local function collect()
	return setmetatable({}, collect_mt)
end

local function querygroup(state, name)
	if not state.groups[name] then
		local setshape = collect()
		state.rules("group", {name=name, setshape=setshape})
		local ok, g = pcall(
			driver.addgroup,
			state.graph,
			name
		)
		checkp(ok, g, "group: %s", name)
		state.groups[name] = {obj=g, shape=setshape.value}
	end
	return state.groups[name]
end

local function queryvar(state, name)
	if not state.vars[name] then
		local setcts = collect()
		local setjfunc = collect()
		state.rules("var", {name=name, setcts=setcts, setjfunc=setjfunc})
		local group = querygroup(state, lib.groupof(name)).obj
		local ok, v = pcall(driver.addvar, state.graph, group, name, setcts.value)
		checkp(ok, v, "var: %s")
		state.vars[name] = {obj=v, jfunc=setjfunc.value}
	end
	return state.vars[name]
end

local function querylabel(state, name)
	if not state.labels[name] then
		local setvalue = collect()
		state.rules("label", {name=name, setvalue=setvalue})
		state.labels[name] = setvalue.value or error(string.format("missing label: `%s'", name))
	end
	return state.labels[name]
end

local function unlabel(state, arg)
	if type(arg) == "string" then
		return querylabel(state, arg)
	elseif type(arg) == "table" then
		local out = {}
		for i,v in ipairs(arg) do
			out[i] = unlabel(state, v)
		end
		return out
	else
		return arg
	end
end

local function isimplicit(name)
	return name:sub(1,11) == "(implicit):"
end

local function queryguard(state, name)
	if not state.guards[name] then
		if isimplicit(name) then
			error(string.format("implicit guard referenced explicitly: %s", name))
		end
		local setvar = collect()
		local setop = collect()
		local setarg = collect()
		state.rules("guard", {name=name, setvar=setvar, setop=setop, setarg=setarg})
		local var = queryvar(state, setvar.value or error(string.format("guard missing var: %s", name)))
		local arg = unlabel(state, setarg.value)
		local ok, g = pcall(driver.addguard, state.graph, var, name, setop.value, arg)
		checkp(ok, g, "guard: %s", name)
		state.guards[name] = {obj=g, var=setvar.value}
	end
	return state.guards[name]
end

local builtinmaps = {
	ident = driver.ident,
	space = driver.space,
	only  = driver.only
}

local function querymap2(state, x)
	if builtinmaps[x] then
		return builtinmaps[x]
	end
	if not state.maps[x] then
		local setif = collect()
		local setjf = collect()
		local setff = collect()
		state.rules("map", {name=x, setinverse=setif, setjfunc=setjf, setflags=setff})
		local inverse = setif.value or error(string.format("missing inverse: %s", x))
		if state.maps[inverse] then
			error(string.format("nonsymmetic inverse %s <-> %s", x, inverse))
		end
		local setii = collect()
		local setji = collect()
		local setfi = collect()
		state.rules("map", {name=inverse, setinverse=setii, setjfunc=setji, setflags=setfi})
		if setii.value ~= x then
			error(string.format("nonsymmetic inverse: %s <-> %s <-> %s", x, inverse, setii.value))
		end
		local ok, fwd = pcall(driver.addmap, state.graph, setff.value, x)
		checkp(ok, fwd, "map: %s", x)
		local ok, inv = pcall(driver.addmap, state.graph, setfi.value, inverse)
		checkp(ok, inv, "map: %s", inverse)
		state.maps[x] = {obj=fwd, map2=driver.umap2(fwd, inv), jfunc=setjf.value}
		state.maps[inverse] = {obj=inv, map2=driver.umap2(inv, fwd), jfunc=setji.value}
	end
	return state.maps[x].map2
end

local function defaultmap(from, to)
	if lib.groupof(from) == lib.groupof(to) then
		return "ident"
	end
end

local function queryedge(state, model, edge)
	local query = {
		model     = model,
		var       = edge.var,
		cts       = edge.cts,
		setcts    = (not edge.cts) and collect(),
		map       = edge.map,
		setmap    = (not edge.map) and collect(),
		rank      = edge.rank,
		setrank   = (not edge.rank) and collect()
	}
	state.rules("edge", query)
	return {
		var    = queryvar(state, edge.var),
		cts    = edge.cts or query.setcts.value,
		rank   = edge.rank or query.setrank.value,
		map2   = querymap2(
			state,
			edge.map
			or query.setmap.value
			or defaultmap(model, edge.var)
			or error(string.format("no map: %s->%s", model, edge.var))
		)
	}
end

local function querycheck(state, model, guard, map)
	local guard = queryguard(state, guard)
	if not map then
		local setmap = collect()
		state.rules("edge", {model=model, var=guard.var, setmap=setmap})
		map = setmap.value
			or defaultmap(model, guard.var)
			or error(string.format("no map: %s->%s", model, guard.var))
	end
	return {
		guard = guard,
		map2  = querymap2(state, map)
	}
end

---- building ----------------------------------------

local function checkmodel(state, name)
	return state.models[name] or error(string.format("undefined model: %s", name))
end

local function cost(state, name, k, c)
	local ok, e = pcall(driver.setcost, state.graph, checkmodel(state, name).obj, k or state.k, c or state.c)
	checkp(ok, e, "model: %s", name)
end

local function edge(var, map, cts, rank)
	return {var=var, map=map, cts=cts, rank=rank}
end

local function ret(state, name, edge)
	local model = checkmodel(state, name)
	if model.skip then return end
	local ex = queryedge(state, name, edge)
	if ex.var.jfunc then
		-- model is trying to return a given variable.
		-- we don't want it in the final graph, ensure it will be skipped in layout phase.
		cost(model, math.huge, 1)
		model.skip = true
		return
	end
	-- pruner will never change var type (given/computed), so this is valid.
	ex.var.computed = true
	driver.setctype(ex.var.obj, ex.cts)
	local ok, e = pcall(driver.addreturn, state.graph, model.obj, ex.var.obj, ex.map2)
	checkp(ok, e, "return(#%d): %s->%s", #model.obj.returns+1, name, edge.var)
	if ex.rank then driver.setrank(e, ex.rank) end
end

local function param(state, name, edge)
	local model = checkmodel(state, name)
	if model.skip then return end
	local ex = queryedge(state, name, edge)
	driver.setctype(ex.var.obj, ex.cts)
	local ok, e = pcall(driver.addparam, state.graph, model.obj, ex.var.obj, ex.map2)
	checkp(ok, e, "param(#%d): %s->%s", #model.obj.params+1, name, edge.var)
	if ex.rank then driver.setrank(e, ex.rank) end
end

local function check(state, name, guard, map, penalty)
	local model = checkmodel(state, name)
	if model.skip then return end
	local cx = querycheck(state, name, guard, map)
	local ok, e = pcall(driver.addcheck, state.graph, model.obj, cx.guard.obj, cx.map2, penalty)
	checkp(ok, e, "check: %s->%s", name, guard)
end

local function impl(state, name, lang, args)
	local model = checkmodel(state, name)
	model.lang = lang
	model.args = args
end

local function model(state, name, k, c)
	local model = state.models[name]
	if model then
		if (k or c) then
			cost(model, k, c)
		end
	else
		local group = querygroup(state, lib.groupof(name)).obj
		local ok, m = pcall(driver.addmodel, state.graph, group, k or state.k, c or state.c, name)
		checkp(ok, m, "model: %s", name)
		model = {obj=m}
		state.models[name] = model
	end
	return model
end

local function implicitguard(state, var, op, arg)
	local arg = unlabel(state, arg)
	local argname
	if type(arg) == "table" then
		table.sort(arg)
		argname = table.concat(arg, ",")
	else
		argname = tostring(arg)
	end
	local name = string.format("(implicit):%s%s%s", var, op, argname)
	if not state.guards[name] then
		local ok, g = pcall(driver.addguard, state.graph, queryvar(state, var).obj, name, op, arg)
		checkp(ok, g, "guard: %s", name)
		state.guards[name] = {obj=g, var=var}
	end
	return name
end

local function getgroup(state, name)
	return querygroup(state, name).obj
end

local function root(state, var)
	local var = queryvar(state, var)
	driver.pin(state.graph, var.obj)
	return var.obj
end

local function typehint(state, var, cts)
	driver.setctype(queryvar(state, var).obj, cts)
end

local function gmodel(state, def)
	local name = def.name
	if model(state, name).skip then return end
	for _,attr in ipairs(def.decl) do
		if attr.tag == "param" then
			param(state, name, edge(attr.name, attr.map, attr.cts, attr.rank))
		elseif attr.tag == "return" then
			ret(state, name, edge(attr.name, attr.map, attr.cts, attr.rank))
			if state.models[name].skip then return end
		elseif attr.tag == "check" then
			check(state, name, implicitguard(state, attr.name, attr.op, attr.arg), attr.map, attr.penalty)
		elseif attr.tag == "cost" then
			cost(state, name, attr.k, attr.c)
		elseif attr.tag == "impl" then
			impl(state, name, attr.lang, attr.args)
		end
	end
end

local function decl(state, ...)
	for _,attr in ipairs({...}) do
		if attr.tag == "model" then
			gmodel(state, attr)
		end
	end
end

local function read(state, ...)
	for _,x in ipairs({...}) do
		if type(x) == "string" or type(x) == "function" then
			glib.read(function(d) decl(state, d) end, x)
		else
			decl(state, x)
		end
	end
end

local function trapvar(state, name)
	local group = querygroup(state, lib.groupof(name))
	local ok, m = pcall(driver.addmodel, state.graph, group.obj, math.huge, 1, string.format("trap<%s>", name))
	checkp(ok, m, "trap model of var: %s", name)
	local var = queryvar(state, name)
	local ok, e = pcall(driver.addreturn, state.graph, m, var.obj, driver.ident)
	checkp(ok, e, "return edge of trap model: %s", name)
end

local function emithook(state, what, name, obj, fb)
	state.rules(what, {name=name, obj=obj, fb=fb})
end

local function buildgraph(state)
	local graph = state.graph
	for name,v in pairs(state.vars) do
		if not (v.computed or v.jfunc) then
			trapvar(state, name)
			v.computed = true
		end
	end
	driver.prune(graph)
	driver.layout(graph)
	local fb = driver.fbuf()
	for name,v in pairs(state.vars) do
		if v.obj.idx and not v.computed then
			if v.jfunc then
				emithook(state, "emit.pre", name, v.obj, fb)
				v.jfunc(fb, v.obj)
				emithook(state, "emit.post", name, v.obj, fb)
			else
				driver.trap(fb, {mes=string.format("access variable without jfunc: %s", name)})
			end
			driver.jfunc(state.graph, v.obj, fb)
			driver.reset(fb)
		end
	end
	for name,m in pairs(state.maps) do
		if m.obj.idx then
			if m.jfunc then
				emithook(state, "emit.pre", name, m.obj, fb)
				m.jfunc(fb, m.obj)
				emithook(state, "emit.post", name, m.obj, fb)
			else
				driver.trap(fb, {mes=string.format("access map without jfunc: %s", name)})
			end
			driver.jfunc(state.graph, m.obj, fb)
			driver.reset(fb)
		end
	end
	for name,m in pairs(state.models) do
		if m.obj.idx then
			-- note: if needed we can also consult rules for the implementation here.
			local impljfunc = driver.loadlang(state.graph, m.lang)
			if impljfunc then
				emithook(state, "emit.pre", name, m.obj, fb)
				impljfunc(fb, m.obj, unpack(m.args))
				emithook(state, "emit.post", name, m.obj, fb)
			else
				driver.trap(fb, {
					mes = string.format("no implementation for language: %s (of model: %s)",
						m.lang,
						name
					)
				})
			end
			driver.jfunc(state.graph, m.obj, fb)
			driver.reset(fb)
		end
	end
	driver.jtab(graph)
	return graph
end

local function unroll2(fs, name)
	if #fs == 0 then return function() end end
	if #fs == 1 then return fs[1] end
	local src = buffer.new()
	src:put("local f1")
	for i=2, #fs do
		src:putf(", f%d", i)
	end
	src:put("= ...\n")
	src:put("return function(S, X)\n")
	for i=1, #fs do
		src:putf("f%d(S, X)\n", i)
	end
	src:put("end\n")
	return load(src, name)(unpack(fs))
end

local function buildinit(state)
	local fs = {}
	local fb = driver.fbuf()
	for name,group in pairs(state.groups) do
		if group.obj.idx then
			if not group.shape then
				error(string.format("group missing shape: %s", name))
			end
			driver.reset(fb)
			emithook(state, "emit.pre", name, group.obj, fb)
			driver.setshape(fb, {group=group.obj, value=group.shape})
			emithook(state, "emit.post", name, group.obj, fb)
			table.insert(fs, driver.ffunc(state.graph, fb))
		end
	end
	return unroll2(fs, "=fhk:init")
end

---- rules ----------------------------------------

local function composite(rules)
	if #rules == 1 then
		return rules[1]
	else
		return function(what, x)
			for _,r in ipairs(rules) do
				r(what, x)
			end
		end
	end
end

local function group(name, ...)
	local rules = composite({...})
	return function(what, x)
		if what == "group" and x.name ~= name then return end
		if what == "var" and lib.groupof(x.name) ~= name then return end
		if what == "edge" and lib.groupof(x.model) ~= name then return end
		return rules(what, x)
	end
end

local function tagged(what_, ...)
	local rules = composite({...})
	return function(what, x)
		if what_ == what then
			return rules(what, x)
		end
	end
end

local function named(name, ...)
	local rules = composite({...})
	return function(what, x)
		if x.name and lib.matchname(x.name, name) then
			return rules(what, x)
		end
	end
end

local function virtual(name, value, ctype)
	-- TODO: this can be specialized when value isn't a function (eg. vrefk)
	local func = type(value) == "function" and value or function() return value end
	return tagged("var", function(_, event)
		if lib.matchname(name, event.name) then
			event.setjfunc(function(fb, var)
				driver.vrefv(fb, {
					f = func,
					var = var
				})
			end)
			if ctype then
				event.setcts(ctype)
			end
		end
	end)
end

local function setshape(shape)
	return tagged("group", function(_, event)
		event.setshape(shape)
	end)
end

local function shape(...)
	return setshape({...})
end

local function shapeof(...)
	local value = {...}
	for i,x in ipairs(value) do
		value[i] = load([[
			local x = ...
			return function()
				return #x
			end
		]], "=fhk: shapeof")(x)
	end
	return setshape(value)
end

local function parserule(src)
	if src:sub(1, 1) == "!" then
		local rule = parserule(src:sub(2))
		return function(...) return not rule(...) end
	end
	if src:match("|") then
		local rules = {}
		for x in src:gmatch("([^|])+") do
			table.insert(rules, parserule(x))
		end
		return function(a, b)
			for _,r in ipairs(rules) do
				if r(a, b) then
					return true
				end
				return false
			end
		end
	end
	if src == "$" then
		return function(a, b) return a == b end
	end
	return function(name)
		return name == src
	end
end

local function true_()
	return true
end

-- rule syntax:
--     [!]from1|from2|...|fromN=>[!]to1|to2|...|toM
-- the bang (!) is optional and inverts the entire selection.
-- the pipe (|) is an OR operator.
-- fromX and toX are literal group names, or $ for the group on the other side of the edge.
local function edgerule(rule, apply)
	local from, to = rule:gsub("%s", ""):match("^([^=]*)=>(.*)$")
	from = from ~= "" and parserule(from) or true_
	to = to ~= "" and parserule(to) or true_
	return tagged("edge", function(_, event)
		local mgroup, vgroup = lib.groupof(event.model), lib.groupof(event.var)
		if not from(mgroup, vgroup) then return end
		if not to(vgroup, mgroup) then return end
		if apply.map and event.setmap then event.setmap(apply.map) end
		if apply.cts and event.setcts then event.setcts(apply.cts) end
		if apply.rank and event.setrank then event.setrank(apply.rank) end
	end)
end

local function parsemap(def)
	local name, flags = def:match("^([^%(]*)%((.*)%)$")
	if not name then error(string.format("syntax error (map1): %s", def)) end
	return name, flags
end

-- def syntax:
--     fwdname(flags)[:invname(flags)]
local function map(def, fwd, inv)
	local fwddef, invdef = def:match("^([^:]*):(.*)$")
	if not fwddef then error(string.format("syntax error (map2): %s", def)) end
	local fwdname, fwdflags = parsemap(fwddef)
	local invname, invflags = parsemap(invdef)
	if invname == "" then invname = string.format("%s@inv", fwdname) end
	return tagged("map", function(_, event)
		if event.name == fwdname then
			event.setinverse(invname)
			event.setflags(fwdflags)
			event.setjfunc(function(fb, map) driver.mapcallf(fb, {f=fwd, map=map}) end)
		end
		if event.name == invname then
			event.setinverse(fwdname)
			event.setflags(invflags)
			event.setjfunc(function(fb, map) driver.mapcallf(fb, {f=inv, map=map}) end)
		end
	end)
end

local function label(labels)
	return tagged("label", function(_, event)
		if labels[event.name] then
			event.setvalue(labels[event.name])
		end
	end)
end

--------------------------------------------------------------------------------

return {
	newstate    = newstate,
	cost        = cost,
	edge        = edge,
	ret         = ret,
	param       = param,
	check       = check,
	impl        = impl,
	model       = model,
	getgroup    = getgroup,
	root        = root,
	typehint    = typehint,
	decl        = decl,
	read        = read,
	buildgraph  = buildgraph,
	buildinit   = buildinit,
	composite   = composite,
	group       = group,
	tagged      = tagged,
	named       = named,
	virtual     = virtual,
	shape       = shape,
	shapeof     = shapeof,
	edgerule    = edgerule,
	map         = map,
	label       = label
}
