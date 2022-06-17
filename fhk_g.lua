local lib = require "fhk_lib"

local function mmmod_set(k)
	return function(v)
		return function(x)
			x[k] = v
		end
	end
end

local mmod_tag   = mmmod_set "tag"
local mod_param  = mmod_tag "param"
local mod_return = mmod_tag "return"
local mod_check  = mmod_tag "check"

local function params(v) return {modifier=mod_param, value=v} end
local function returns(v) return {modifier=mod_return, value=v} end
local function check(v) return {modifier=mod_check, value=v} end
local function cost(kc) return {primitive=true, value={tag="cost", k=kc.k, c=kc.c}} end
local derived = cost({k=0, c=1})

local function mprim_impl(lang)
	return function(...)
		return {primitive=true, value={tag="impl", lang=lang, args={...}}}
	end
end
local impl = setmetatable({}, {
	__index = function(impl, lang)
		impl[lang] = mprim_impl(lang)
		return impl[lang]
	end
})

local function mmmod_check(op)
	return function(v)
		return function(x)
			x.tag = "check"
			x.op = op
			x.arg = v
		end
	end
end

local infix_mt
local function isinfix(x) return type(x) == "table" and x.infix end
local function infix(f) return setmetatable({f=f}, infix_mt) end
infix_mt = {
	__index = { infix=true },
	__mul = function(left, right)
		if isinfix(left) then
			if isinfix(right) then
				local f, g = left.f, right.f
				return infix(function(x) return g(f(x)) end)
			end
			return {modifier=left.f, value=right}
		else
			return {modifier=right.f, value=left}
		end
	end
}

local function checktab(x)
	return type(x) == "table" and x or {x}
end

local function tabf(f)
	return function(x)
		return f(checktab(x))
	end
end

local function infixmod(f)
	return function(...)
		return infix(f(...))
	end
end

local as      = infixmod(mmmod_set "cts")
local choose  = infixmod(mmmod_set "map")
local penalty = infixmod(mmmod_set "penalty")
local is      = infixmod(tabf(mmmod_check "&"))
local is_not  = infixmod(tabf(mmmod_check "!&"))
local gt      = infixmod(mmmod_check ">")
local ge      = infixmod(mmmod_check ">=")
local lt      = infixmod(mmmod_check "<")
local le      = infixmod(mmmod_check "<=")

local function push(ctx, f)
	ctx.top = ctx.top + 1
	ctx.stack[ctx.top] = f
end

local function _canonicalize(ctx, x)
	if type(x) == "string" then
		if not x:match("#") then
			if not ctx.owner then error(string.format("ambiguous variable name: %s", x)) end
			x = lib.groupof(ctx.owner) .. "#" .. x
		end
		local out = { name=x }
		for i=0, ctx.top do
			ctx.stack[i](out)
		end
		table.insert(ctx.out, out)
	elseif type(x) == "function" then
		-- note: unmodified
		table.insert(ctx.out, impl.LuaJIT(x).value)
	elseif x.primitive then
		-- note: unmodified
		table.insert(ctx.out, x.value)
	else
		local top = ctx.top
		if #x > 0 then
			for _,e in ipairs(x) do
				if e == "->" then
					push(ctx, mod_return)
				else
					_canonicalize(ctx, e)
				end
			end
		elseif x.modifier then
			push(ctx, x.modifier)
			_canonicalize(ctx, x.value)
		else
			error(string.format("unexpected `%s'", x))
		end
		ctx.top = top
	end
end

-- decl :: {decl}
--       | modifier(decl)
--       | string
--       | param(...)
--       | returns(...)
--       | check(...)
--       | impl
--       | cost
local function canonicalize(decl, owner)
	local ctx = { owner=owner, out={}, stack={[0]=mod_param}, top=0 }
	_canonicalize(ctx, decl)
	return ctx.out
end

local function model(name, ...)
	return {tag="model", name=name, decl=canonicalize({...}, name)}
end

local function derive(ret, ...)
	if type(ret) == "string" then
		local mod = model(ret, derived, ...)
		for _,attr in ipairs(mod.decl) do
			if attr.tag == "return" then
				return mod
			end
		end
		table.insert(mod.decl, {tag="return", name=ret})
		return mod
	else
		ret = canonicalize(returns(ret))
		local group
		local names = {}
		for _,attr in ipairs(ret) do
			if attr.tag ~= "return" then
				error(string.format("unexpected %s in derive", attr.tag))
			end
			local g,n = lib.groupof(attr.name)
			if group and group ~= g then
				error(string.format("ambiguous derive group: %s / %s", group, g))
			end
			group = g
			table.insert(names, n)
		end
		local mod = model(string.format("%s#%s", group, table.concat(names, ",")), derived, ...)
		for _,r in ipairs(ret) do
			table.insert(mod.decl, r)
		end
		return mod
	end
end

local function envread(env, fname)
	local f, err = loadfile(fname or error("read: expected file name"), nil, env)
	if not f then error(string.format("read: error (%s): %s", fname, err)) end
	return f()
end

local function envreadf(env)
	return function(f)
		if type(f) == "function" then
			return setfenv(f, env)()
		elseif type(f) == "string" then
			return envread(env, f)
		else
			error(string.format("unexpected parameter to read: %s", f))
		end
	end
end

local function env(visit)
	local env   = setmetatable({}, {__index=_G})
	env.read    = envreadf(env)
	env.model   = function(name) return function(...) return visit(model(name, ...)) end end
	env.derive  = function(ret) return function(...) return visit(derive(ret, ...)) end end
	env.params  = params
	env.returns = returns
	env.check   = check
	env.cost    = cost
	env.impl    = impl
	env.as      = as
	env.choose  = choose
	env.penalty = penalty
	env.is      = is
	env.is_not  = is_not
	env.gt      = gt
	env.ge      = ge
	env.lt      = lt
	env.le      = le
	return env
end

local function read(visit, ...)
	local env = env(visit)
	for _,f in ipairs({...}) do
		env.read(f)
	end
end

--------------------------------------------------------------------------------

return {
	params  = params,
	returns = returns,
	check   = check,
	cost    = cost,
	impl    = impl,
	as      = as,
	choose  = choose,
	penalty = penalty,
	is      = is,
	is_not  = is_not,
	gt      = gt,
	ge      = ge,
	lt      = lt,
	le      = le,
	model   = model,
	derive  = derive,
	env     = env,
	read    = read
}
