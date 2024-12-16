local ffi = require "ffi"
local buffer = require "string.buffer"

local libname
if jit.os == "Windows" then
	libname = "fhk.dll"
else
	libname = "libfhk.so"
end
local target = os.getenv("FHK_TARGET") or "debug"
local fhk = assert(package.loadlib("../target/"..target.."/"..libname, "luaopen_fhk"))()

---- asserts -------------------------------------------------------------------

local function equal(a, b, tol)
	if type(a) ~= type(b) then
		return false
	end
	if type(a) == "number" then
		if tol then
			return math.abs(a-b) <= tol
		else
			return a == b
		end
	end
	if #a ~= #b then
		return false
	end
	for i=1, #a do
		if not equal(a[i], b[i]) then
			return false
		end
	end
	return true
end

local function prettyprint(x)
	if type(x) ~= "table" then
		return tostring(x)
	end
	local buf = buffer.new()
	buf:put("[")
	for i=1, #x do
		local v = x[i]
		buf:put(" ")
		if type(v) == "table" then
			buf:put(prettyprint(v))
		else
			buf:put(v)
		end
	end
	buf:put("]")
	return tostring(buf)
end

local function check(computed, true_, tol)
	for i,t in ipairs(true_) do
		local c = computed[i]
		if type(c) == "cdata" then
			c = c:totable()
		end
		local ok
		if type(t) == "function" then
			ok = t(c)
		else
			ok = equal(t,c,tol)
		end
		if not ok then
			error(string.format("bad result!\ncomputed: %s\ntrue    : %s\n",
				prettyprint(c), prettyprint(t)))
		end
	end
end

---- test driver ---------------------------------------------------------------

local function test_query(T, tab, ...)
	local query = T.G:newquery(tab)
	for _,expr in ipairs({...}) do
		query:add(expr)
	end
	return query
end

local function test_compile(T)
	if not T.image then
		T.image = assert(T.G:compile())
	end
	return T.image
end

local function test_newinstance(T, prev, mask)
	return test_compile(T):newinstance(T.alloc, nil, prev, mask)
end

local function test_result(T, results)
	local query = T.G:newquery("global")
	local true_ = {}
	for e,v in pairs(results) do
		query:add(e)
		table.insert(true_, v)
	end
	local inst = test_newinstance(T)
	check({query.query(inst):unpack()}, true_)
end

local function pcallfail(message, f, ...)
	local ok, err = pcall(f, ...)
	assert(not ok, "expected fail but succeeded")
	if not err:match(message) then
		error(string.format("bad error message: %s", err))
	end
end

local function test_fail(T, expr, message)
	local query = T.G:newquery("global")
	if type(expr) == "table" then
		for _,e in ipairs(expr) do
			query:add(e)
		end
	else
		query:add(expr)
	end
	local inst = test_newinstance(T)
	pcallfail(message, query.query, inst)
end

local function test_compilefail(T, message)
	pcallfail(message, test_compile, T)
end

ffi.cdef [[
	void *malloc(size_t);
	void free(void *);
]]

local function test_alloc(T, _, size, align)
	print(string.format("[alloc] %d (align: %d)", size, align))
	-- TODO: it would also be a good idea to put some guard pages here
	local p = ffi.C.malloc(size)
	ffi.fill(p, size, 0x29)
	table.insert(T.allocs, p)
	return p
end

local function bind(self,f) return function(...) return f(self, ...) end end

local function testnew()
	local env = setmetatable({
		allocs  = {},
		G       = fhk.newgraph(),
		check   = check
	}, {__index=_G})
	env.query = bind(env, test_query)
	env.result = bind(env, test_result)
	env.fail = bind(env, test_fail)
	env.compile = bind(env, test_compile)
	env.compilefail = bind(env, test_compilefail)
	env.newinstance = bind(env, test_newinstance)
	env.alloc = ffi.cast("void *(*)(void *,size_t,size_t)", bind(env, test_alloc))
	return env
end

local function testfree(T)
	for _,p in ipairs(T.allocs) do
		ffi.C.free(p)
	end
	T.alloc:free()
end

local function flush(T, buf, what)
	-- print(string.format("---- FLUSH (%s) ----", what))
	-- print(buf)
	if what == "directive" then
		assert(load(buf, nil, nil, T))()
	elseif what == "src" then
		T.G:define(buf)
	end
	buf:reset()
end

local function testrun(T, fname)
	local fp = assert(io.open(fname))
	local buf = buffer.new()
	local what
	for line in fp:lines() do
		local linewhat
		if line:sub(1,3) == "###" then
			linewhat = "directive"
			line = line:sub(4)
		else
			linewhat = "src"
		end
		if linewhat ~= what then
			if #buf > 0 then
				flush(T, buf, what)
			end
			what = linewhat
		end
		buf:put(line, "\n")
	end
	fp:close()
	if #buf > 0 then
		flush(T, buf, what)
	end
end

--------------------------------------------------------------------------------

local files = {...}
if #files == 0 then
	-- doesn't work on windows, too bad
	io.popen("ls *.t"):read("*a"):gsub("[^\n]+", function(name) table.insert(files, name) end)
end
io.stdout:write("1..", #files, "\n")
for i,fname in ipairs(files) do
	local T = testnew()
	local ok, err = xpcall(testrun, debug.traceback, T, fname)
	testfree(T)
	if ok then
		io.stdout:write("ok ", i, " - ", fname, "\n")
	else
		io.stdout:write("not ok ", i, " - ", fname, "\n")
		io.stdout:write("# ", err:gsub("\n", "\n# "), "\n")
	end
end
