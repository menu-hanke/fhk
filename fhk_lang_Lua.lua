local driver = require "fhk_driver"
local buffer = require "string.buffer"
local ffi = require "ffi"

local function cedge_inext(e, i)
	i = i+1
	if i < e.n then
		return i, e.p[i]
	end
end

local cedge_mt = {
	__index = function(self, i)
		return self.p[i]
	end,

	__newindex = function(self, i, v)
		self.p[i] = v
	end,

	__len = function(self)
		return tonumber(self.n)
	end,

	__ipairs = function(self)
		return cedge_inext, self, -1
	end,

	__tostring = function(self)
		local buf = {}
		for _,v in ipairs(self) do
			table.insert(buf, tostring(v))
		end
		return string.format("[%s]", table.concat(buf, ", "))
	end
}

local function cedge_ct_new(ctype)
	return ffi.metatype(
		ffi.typeof([[
			struct {
				$ *p;
				size_t n;
			}
		]], ctype),
		cedge_mt
	)
end

local cedge_cts = {}
local function edgect(ctype)
	local ctid = tonumber(ctype)
	if not cedge_cts[ctid] then
		cedge_cts[ctid] = cedge_ct_new(ctype)
	end
	return cedge_cts[ctid]
end

local function sigct(model)
	local buf = buffer.new()
	buf:put("struct {\n")
	local cts = {}
	for i,p in ipairs(model.params) do
		buf:putf("$ param%d;\n", i)
		table.insert(cts, edgect(p.var.ctype))
	end
	for i,r in ipairs(model.returns) do
		buf:putf("$ return%d;\n", i)
		table.insert(cts, edgect(r.var.ctype))
	end
	buf:put("}")
	return ffi.typeof(tostring(buf), unpack(cts))
end

local function cache(f)
	local cache = setmetatable({}, {
		__mode = "v",
		__index = function(self, ctid)
			self[ctid] = f()
			return self[ctid]
		end
	})
	return function(ctid)
		return cache[ctid]
	end
end

local convctab_func = cache(function()
	return load([[
		local new = ...
		return function(edge)
			local out = new(#edge, 0)
			for i=0, #edge-1 do
				out[i+1] = edge.p[i]
			end
			return out
		end
	]])(table.new)
end)

local convtabc_func = cache(function()
	return load([[
		return function(edge, tab)
			for i=0, #edge-1 do
				edge.p[i] = tab[i+1]
			end
		end
	]])()
end)

-- modcall lua function w/ lua table conversion
local function modcalllua(J, o, f)
	local params, returns, conv = {}, {}, {}
	local mode = driver.overridemode(driver.getmode(o), o.impl.signature)
	local code = driver.code()
	for i,r in ipairs(o.returns) do
		if mode:sub(#o.params+i,#o.params+i) == "s" then
			returns[i] = string.format("call.return%d[0]", i)
		else
			code.src:putf("local return%d\n", i)
			returns[i] = string.format("return%d", i)
			local ctid = tonumber(r.var.ctype)
			code.upv[string.format("convtabc%d", ctid)] = convtabc_func(ctid)
			table.insert(conv, string.format("convtabc%d(call.return%d,return%d)", ctid, i, i))
		end
	end
	for i,p in ipairs(o.params) do
		if mode:sub(i,i) == "s" then
			params[i] = string.format("call.param%d[0]", i)
		else
			local ctid = tonumber(p.var.ctype)
			code.upv[string.format("convctab%d", ctid)] = convctab_func(ctid)
			params[i] = string.format("convctab%d(call.param%d)", ctid, i)
		end
	end
	local fv = code:upval(f)
	local ct = code:upval(ffi.typeof("$*", sigct(o)))
	code.upv.cast = ffi.cast
	code.src:putf("local call = cast(%s, S.edges)\n", ct)
	code.src:putf("%s = %s(%s)\n", table.concat(returns, ","), fv, table.concat(params, ","))
	code.src:putf("%s\n", table.concat(conv, "\n"))
	code.name = string.format("=fhk:modcalllua<%s>@%s", driver.desc(o), driver.funcname(f))
	return code:emitjmp(J)
end

-- modcall lua function w/ ffi structs
local function modcallffi(J, o, f)
	local params, returns = {}, {}
	local mode = driver.overridemode(driver.getmode(o), o.impl.signature):gmatch(".")
	for i=1, #o.params do
		if mode() == "s" then
			table.insert(params, string.format("call.param%d[0]", i))
		else
			table.insert(params, string.format("call.param%d", i))
		end
	end
	for i=1, #o.returns do
		if mode() == "s" then
			table.insert(returns, string.format("call.return%d[0]", i))
		else
			table.insert(params, string.format("call.return%d", i))
		end
	end
	local code = driver.code()
	local fv = code:upval(f)
	local ct = code:upval(ffi.typeof("$*", sigct(o)))
	code.upv.cast = ffi.cast
	code.src:putf("local call = cast(%s, S.edges)\n", ct)
	if #returns > 0 then
		code.src:putf("%s = ", table.concat(returns, ", "))
	end
	code.src:putf("%s(%s)", fv, table.concat(params, ", "))
	code.name = string.format("=fhk:modcallffi<%s>@%s", driver.desc(o), driver.funcname(f))
	return code:emitjmp(J)
end

local function lua_load(J, o)
	if type(o.impl[1]) == "string" then
		func = require(o.impl[1])
		for i=2, #o.impl do
			func = func[o.impl[i]]
		end
	else
		func = o.impl[1]
	end
	if o.impl.load then
		func = o.impl.load(func)
	end
	if o.impl.mode == "ffi" then
		return modcallffi(J, o, func)
	else
		return modcalllua(J, o, func)
	end
end

--------------------------------------------------------------------------------

return {
	load = lua_load
}
