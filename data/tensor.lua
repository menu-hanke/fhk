local ffi = require "ffi"
local buffer = require "string.buffer"

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
local PRI_PTR = 11
local PRI_STR = 12
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
	[PRI_PTR] = ffi.typeof("void *"),
	[PRI_STR] = nil, -- TODO: const char *? should these be null terminated?
}

-- it's logically an uint32_t, but signed generates slightly better code
local IDX_CTYPE = "int32_t"

-- ctid -> {e,n}
local METADATA = {}

-- ctid(e) | (n<<8)  ->  ct
local CTYPES = {}

local function metadata(t)
	return METADATA[tonumber(t)]
end

local function putrep(buf, s, n)
	for _=1, n do buf:put(s) end
end

local function putflatrepr(e, buf, indir)
	local meta = metadata(e)
	if meta then
		putflatrepr(meta.e, buf, indir+1)
		buf:put(IDX_CTYPE, " ")
		putrep(buf, "*", indir)
		buf:putf("n%d[%d];\n", indir, meta.n)
	else
		buf:put("$ ")
		putrep(buf, "*", indir)
		buf:put("e;\n")
	end
end

local function makegetter(e, n)
	local buf = buffer.new()
	buf:put("return function(self")
	for i=1, n do buf:putf(", i%d", i) end
	buf:put(")\n")
	local meta = metadata(e)
	if meta then
		error("TODO")
	else
		if n > 1 then
			error("TODO")
		end
		buf:put("return self.e[i1]\n")
	end
	buf:put("end")
	return load(buf)()
end

local function maketotab(n)
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
			buf:put(")\n")
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
			buf:put(v)
		end
	end
	buf:put(" ]")
end

local function tensor__tostring(tensor)
	local buf = buffer.new()
	puttab(buf, tensor:totable())
	return tostring(buf)
end

local function newmetatype(e, n)
	local shape = makeshape(n)
	local mt = {
		__index = {
			get     = makegetter(e, n),
			totable = maketotab(n),
			shape   = shape
		},
		__len      = shape,
		__tostring = tensor__tostring,
	}
	return mt
end

local function ctkey(e, n)
	return bit.lshift(tonumber(e), 8) + n
end

local function scalar_ctype(pri)
	return PRI_CT[pri]
end

local function vector_ctype(e)
	error("TODO")
end

-- struct layout here must match query memory layout.
local function tensor_ctype(e, n)
	e = ffi.typeof(e)
	if (not n) or n == 0 then return e end
	local ctk = ctkey(e, n)
	local ct = CTYPES[ctk]
	if ct then return ct end
	local buf = buffer.new()
	buf:put("struct {\n")
	putflatrepr(e, buf, 1)
	buf:putf("%s n[%d];\n}", IDX_CTYPE, n)
	ct = ffi.typeof(tostring(buf), e)
	METADATA[tonumber(ct)] = {e=e, n=n}
	CTYPES[ctk] = ct
	return ffi.metatype(ct, newmetatype(e, n))
end

return {
	scalar_ctype = scalar_ctype,
	vector_ctype = vector_ctype,
	tensor_ctype = tensor_ctype
}
