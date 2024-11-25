local ffi = require "ffi"
local buffer = require "string.buffer"

local libname
if jit.os == "Windows" then
	libname = "fhk.dll"
else
	libname = "libfhk.so"
end
local target = os.getenv("FHK_TARGET") or "debug"
local dump = os.getenv("FHK_DUMP") or ""
local fhk = assert(package.loadlib("../target/"..target.."/"..libname, "luaopen_fhk"))()

---- asserts -------------------------------------------------------------------

local function near(x, tol)
	-- consider: need relative tolerance here?
	tol = tol or 1e-6
	return function(v)
		return math.abs(x-v) <= tol
	end
end

local function veceq(tab, v)
	if #tab ~= #v then
		return false, string.format("expected %d items, got %d", #tab, #v)
	end
	local mismatch = {}
	for i=1, #v do
		if tab[i] ~= v[i-1] then
			table.insert(mismatch, string.format("    [%d]: %g ~= %g\n", i-1, tab[i], v[i-1]))
		end
	end
	if #mismatch > 0 then
		return false, string.format("mismatched elements: \n%s", table.concat(mismatch))
	else
		return true
	end
end

local function scalareq(x, y)
	if x == y then
		return true
	else
		return false, string.format("%s ~= %s", x, y)
	end
end

local function check(computed, true_)
	for i,r in ipairs(true_) do
		if type(computed[i]) == "cdata" then
			assert(veceq(r, computed[i]))
		elseif type(r) == "number" or type(r) == "boolean" then
			assert(scalareq(computed[i], r))
		else
			assert(r(computed[i]))
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

local function test_result(T, results)
	local exprs, values = {}, {}
	for e,v in pairs(results) do
		table.insert(exprs, e)
		table.insert(values, v)
	end
	table.insert(T.results, {query=test_query(T, "global", unpack(exprs)), true_=values})
end

local function test_flush(T)
	if #T.buf > 0 then
		T.G:define(T.buf)
		T.buf:reset()
	end
end

local function test_compile(T)
	if not T.image then
		test_flush(T)
		if dump:match("o") then
			-- XXX move this after compile when the compiler actually works
			io.stderr:write(T.G:dump(dump), "\n")
		end
		T.image = assert(T.G:compile())
	end
end

local function test_newinstance(T, prev, mask)
	return T.image:newinstance(T.alloc, nil, prev, mask)
end

local function test_checkresults(T)
	test_compile(T)
	local inst = test_newinstance(T)
	for _,r in ipairs(T.results) do
		check({r.query.query(inst):unpack()}, r.true_)
	end
end

ffi.cdef [[
	void *malloc(size_t);
	void free(void *);
]]

local function test_alloc(T, _, size, align)
	print(string.format("[alloc] %d (align: %d)", size, align))
	local p = ffi.C.malloc(size)
	table.insert(T.allocs, p)
	return p
end

local function bind(self,f) return function(...) return f(self, ...) end end

local function testnew()
	local env = setmetatable({
		allocs  = {},
		results = {},
		buf     = buffer.new(),
		G       = fhk.newgraph(),
		near    = near,
		check   = check
	}, {__index=_G})
	env.query = bind(env, test_query)
	env.result = bind(env, test_result)
	env.compile = bind(env, test_compile)
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

local function testrun(T, fname)
	local fp = assert(io.open(fname))
	for line in fp:lines() do
		if line:sub(1,3) == "###" then
			test_flush(T)
			assert(load(line:sub(4), nil, nil, T))()
		elseif not line:match("^%s*$") then
			T.buf:put(line, "\n")
		end
	end
	fp:close()
	if #T.results > 0 then
		test_checkresults(T)
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
