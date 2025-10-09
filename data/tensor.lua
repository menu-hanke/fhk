local ffi = require "ffi"
local buffer = require "string.buffer"

-- it's logically an uint32_t, but signed generates slightly better code
local IDX_CTYPE = "int32_t"

---- Scalars -------------------------------------------------------------------

-- ORDER PRI
local PRI_F64 = 0
local PRI_F32 = 1
local PRI_I64 = 2
local PRI_I32 = 3
local PRI_I16 = 4
local PRI_I8  = 5
local PRI_U64 = 6
local PRI_U32 = 7
local PRI_U16 = 8
local PRI_U8  = 9
local PRI_B1  = 10
local PRI_FX  = 11
local PRI_PTR = 12
local PRI_STR = 13
local PRI_CT = {
	[PRI_F64] = ffi.typeof("double"),
	[PRI_F32] = ffi.typeof("float"),
	[PRI_I64] = ffi.typeof("int64_t"),
	[PRI_I32] = ffi.typeof("int32_t"),
	[PRI_I16] = ffi.typeof("int16_t"),
	[PRI_I8]  = ffi.typeof("int8_t"),
	[PRI_U64] = ffi.typeof("uint64_t"),
	[PRI_U32] = ffi.typeof("uint32_t"),
	[PRI_U16] = ffi.typeof("uint16_t"),
	[PRI_U8]  = ffi.typeof("uint8_t"),
	[PRI_B1]  = ffi.typeof("bool"),
	[PRI_FX]  = nil,
	[PRI_PTR] = ffi.typeof("void *"),
	[PRI_STR] = ffi.typeof("const char *")
}

local function scalar_ctype(pri)
	return PRI_CT[pri]
end

---- Tensors -------------------------------------------------------------------
-- tensor ctype representation:
-- * 1-D tensor:
--   struct {
--     elem *e;
--     int32_t n;
--   }
-- * N-D tensor:
--   struct {
--     elem *e;
--     int32_t n[N];
--   }
-- * N-D tensor of M-D tensors (non-rectangular)
--   struct {
--     elem **e;
--     int32_t *n1[M];
--     int32_t n[N];
--   }
-- * general case: N-D tensor of N1-D tensors of ... of NK-D tensors (non-rectangular):
--   struct {
--     elem *(K)* e;
--     int32_t *(K-1)* nK[NK];
--     ...
--     int32_t *n1[N1];
--     int32_t n[N];
--   }

local function xmetadata(x)
	return x["fhk$e"], x["fhk$n"]
end

local function metadata(x)
	local ok, e, n = pcall(xmetadata, x)
	if ok then return e, n end
end

-- TODO: also handle nil indices (slicing) on N-D tensors
local function makegetter(e, n)
	local buf = buffer.new()
	buf:put("return function(self")
	for i=1, n do buf:putf(", i%d", i) end
	buf:put(")\n")
	local ee, en = metadata(e)
	if ee then
		if n > 1 then
			error("TODO")
		end
		buf:put("local r = self['fhk$e']()\nr.e = self.e[i1]\n")
		for i=0, en-1 do
			buf:putf("r.n[%d] = self.n1[%d][i1]\n", i, i)
		end
		buf:put("return r\n")
	else
		if n > 1 then
			error("TODO")
		end
		buf:put("return self.e[i1]\n")
	end
	buf:put("end")
	return load(buf)()
end

local function maketotab(e, n)
	local buf = buffer.new()
	buf:put("return function(self)\nlocal tab0 = {}\n")
	for i=0, n-1 do
		buf:putf("for i%d=0, self.n[%d]-1 do\n", i, i)
		if i == n-1 then
			buf:putf("tab%d[i%d+1] = self:get(", i, i)
			for j=0, n-1 do
				if j > 0 then buf:put(",") end
				buf:putf("i%d", i)
			end
			buf:put(")")
			if metadata(e) then
				buf:put(":totable()")
			end
			buf:put("\n")
		else
			buf:putf("local tab%d = {}\ntab%d[i%d] = tab%d\n", i+1, i, i, i+1)
		end
		buf:put("end\n")
	end
	buf:put("return tab0\nend\n")
	return load(buf)()
end

local function makeshape(n)
	local buf = buffer.new()
	buf:put("return function(self)\nreturn ")
	for i=0, n-1 do
		if i>0 then buf:put(",") end
		buf:putf("self.n[%d]", i)
	end
	buf:put("\nend")
	return load(buf)()
end

local function puttab(buf, tab)
	buf:put("[")
	for i=1, #tab do
		local v = tab[i]
		buf:put(" ")
		if type(v) == "table" then
			puttab(buf, v)
		else
			buf:put(tostring(v))
		end
	end
	buf:put(" ]")
end

local function tensor__tostring(tensor)
	local buf = buffer.new()
	puttab(buf, tensor:totable())
	return tostring(buf)
end

local function vector__newindex(self, i, v)
	self.e[i] = v
end

local function newmetatype(e, n)
	local shape = makeshape(n)
	local get = makegetter(e, n)
	local index = ffi.metatype("struct {}", {
		__index = {
			["fhk$e"] = e,
			["fhk$n"] = n,
			get       = get,
			totable   = maketotab(e, n),
			shape     = shape
		}
	})
	local indexfunc = load([[
		local index = ...
		local get, type = index.get, type
		return function(self, key)
			if type(key) == "number" then
				return get(self, key)
			else
				return index[key]
			end
		end
	]])(index)
	local mt = {
		__index    = indexfunc,
		__len      = shape,
		__tostring = tensor__tostring
	}
	if n == 1 and not metadata(e) then
		-- TODO: add ipairs, too
		mt.__newindex = vector__newindex
	end
	return mt
end

local function putflatrepr(e, buf, i)
	local ee, en = metadata(e)
	if ee then
		putflatrepr(ee, buf, i+1)
		buf:put(IDX_CTYPE, " ", string.rep("*", i), "n", i, "[", en, "];\n")
	else
		buf:put("$ ", string.rep("*", i), " e;\n");
	end
end

-- ctid(e) | (n<<8)  ->  ct
local CTYPES = {}

local function ctkey(e, n)
	return bit.lshift(tonumber(e), 8) + n
end

local function tensor_ctype(e, n)
	e = ffi.typeof(e)
	if (not n) or n == 0 then return e end
	local ctk = ctkey(e, n)
	local ct = CTYPES[ctk]
	if ct then return ct end
	local buf = buffer.new()
	buf:put("struct {\n")
	putflatrepr(e, buf, 1)
	buf:put(IDX_CTYPE, " n[", n, "];\n}")
	local inner = e
	while true do
		local ee = metadata(inner)
		if ee then inner = ee else break end
	end
	ct = ffi.typeof(tostring(buf), inner)
	CTYPES[ctk] = ct
	return ffi.metatype(ct, newmetatype(e, n))
end

local function istensor(x)
	return metadata(x) ~= nil
end

--------------------------------------------------------------------------------

return {
	scalar_ctype = scalar_ctype,
	tensor_ctype = tensor_ctype,
	istensor     = istensor
}
