local ffi = require "ffi"
local buffer = require "string.buffer"

for cmd,var in pairs {
	v = "FHK_LUAJIT_VERBOSE",
	p = "FHK_LUAJIT_PROFILE",
	dump = "FHK_LUAJIT_DUMP"
} do
	local e = os.getenv(var)
	if e then
		require("jit."..cmd).start(cmd ~= "v" and e)
	end
end

-- these are mis-declared on purpose:
-- * we don't care about the second argument of fhk_swap, we only want to pass control to the host
-- * int gives better code than int64_t
local fhk_swap = ffi.cast("int (*)(void *)", (select(2, ...)))

local function cmp_slot(a, b)
	return ffi.alignof(a.ctype) > ffi.alignof(b.ctype)
end

local function layout(funcs)
	local maxsize = 8
	for _,f in ipairs(funcs) do
		local slots = {}
		for _,i in ipairs(f.inputs) do if type(i) == "table" then table.insert(slots, i) end end
		for _,o in ipairs(f.returns) do table.insert(slots, o) end
		table.sort(slots, cmp_slot)
		local cursor = 8 -- first slot is the coroutine stack pointer
		for _,s in ipairs(slots) do
			s.offset = cursor
			cursor = cursor + ffi.sizeof(s.ctype)
		end
		maxsize = math.max(maxsize, cursor)
	end
	return maxsize
end

local function codegen(funcs, base)
	local baseaddr = ffi.cast("intptr_t", base)
	local buf = buffer.new()
	local J = {}
	J[0] = function() end
	for i,f in ipairs(funcs) do
		local loader, err = load(f.load)
		if not loader then return false, err end
		local ok, func = xpcall(loader, debug.traceback)
		if not ok then return false, func end
		buf:put("local func, J, swap, base")
		local upvalues = {func, J, fhk_swap, base}
		for i,input in ipairs(f.inputs) do
			if type(input) == "table" then
				buf:putf(", i%d", i)
				table.insert(upvalues, ffi.cast(ffi.typeof("$*", input.ctype), baseaddr+input.offset))
			end
		end
		for i,o in ipairs(f.returns) do
			buf:putf(", o%d", i)
			table.insert(upvalues, ffi.cast(ffi.typeof("$*", o.ctype), baseaddr+o.offset))
		end
		buf:put(" = ...\nreturn function()\n")
		if #f.returns > 0 then
			-- TODO: tensor returns need a support function call here.
			for i=1, #f.returns do
				if i>1 then buf:put(",") end
				buf:putf("o%d[0]", i)
			end
			buf:put("=")
		end
		buf:put("func(")
		for i=1, #f.template do
			local b = f.template:byte(i,i)
			if b >= 0x80 then
				local idx = b - 0x7f
				if type(f.inputs[idx]) == "number" then
					idx = f.inputs[idx]
				end
				buf:putf("i%d[0]", idx)
			else
				buf:put(string.char(b))
			end
		end
		buf:put(")\nreturn J[swap(base)]()\nend")
		J[i] = load(buf)(unpack(upvalues))
		buf:reset()
	end
	return J
end

local function run(J, mem, fhk_lua_swap_exit)
	fhk_lua_swap_exit = ffi.cast("int (*)(void *, const char *)", fhk_lua_swap_exit)
	local idx = fhk_swap(mem)
	while true do
		local ok, err = xpcall(J[idx], debug.traceback)
		if ok then
			return
		else
			idx = fhk_lua_swap_exit(mem, err)
		end
	end
end

local function makejumptab(funcs)
	local maxsize = layout(funcs)
	local mem = ffi.new("uint64_t[?]", math.ceil(maxsize/8)) -- alloc uint64_t's to ensure alignment.
	_G[mem] = mem -- anchor it to ensure it's not gced.
	mem = ffi.cast("void *", mem)
	local J, err = codegen(funcs, mem)
	if not J then return nil, err end
	_G.__fhk_run = function(...) return run(J, mem, ...) end
	return tonumber(ffi.cast("intptr_t", mem))
end

return makejumptab(...)
