local ffi = require "ffi"
local buffer = require "string.buffer"

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
		buf:putf("for i%d=0, self.n[%d] do\n", i, i)
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
	end
	buf:put("return tab0\nend\n")
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
	buf:put("]")
end

local function tensor__tostring(tensor)
	local buf = buffer.new()
	puttab(buf, tensor:totable())
	return tostring(buf)
end

local function newmetatype(e, n)
	local mt = {
		__index = {
			get     = makegetter(e, n),
			totable = maketotab(n)
		},
		__tostring = tensor__tostring
	}
	return mt
end

local function ctkey(e, n)
	return bit.lshift(tonumber(e), 8) + n
end

-- struct layout here must match query memory layout.
local function ctypeof(e, n)
	e = ffi.typeof(e)
	if (not n) or n == 0 or not metadata(e) then return e end
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
	ctypeof = ctypeof
}
