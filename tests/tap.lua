#!/bin/env luajit

-- assertions
local function fails(f, err)
	if type(f) == "string" then
		return function(g) return fails(g, f) end
	end

	local ok, mes = pcall(f)
	if ok then return false end
	return (not err) or mes:match(err)
end

local test_globals = setmetatable({
	fails = fails
}, { __index = _G })

-- doesn't work on windows, too bad.
local function lstestfiles(out)
	io.popen("ls *.t"):read("*a"):gsub("[^\n]+", function(name) table.insert(out, name) end)
end

local function istest(name)
	return type(name) == "string" and name:sub(1, 5) == "test_"
end

local function loadtests(files)
	local tests = {}
	for _,fname in ipairs(files) do
		local f,err = loadfile(fname, nil, setmetatable({}, {
			__newindex = function(self, k, v)
				if istest(k, v) then
					table.insert(tests, { file=fname, name=k, f=v })
				end
				rawset(self, k, v)
			end,
			__index = test_globals
		}))
		if err then
			io.stderr:write(err, "\n")
			os.exit(2)
		end
		f()
	end
	return tests
end

local function filtertests(tests, accept)
	local out = {}
	for _,test in ipairs(tests) do
		if accept[test.name] then
			table.insert(out, test)
		end
	end
	return out
end

local function tap(tests)
	io.stdout:write("1..", #tests, "\n")
	for i,t in ipairs(tests) do
		local ok, err = xpcall(t.f, debug.traceback)
		if ok then
			io.stdout:write("ok ", i, " - ", t.name, "\n")
		else
			io.stdout:write("not ok ", i, " - ", t.name, "\n")
			io.stdout:write("# ", err:gsub("\n", "\n# "), "\n")
		end
	end
end

local function help()
	io.stderr:write([[
usage: tap.lua [options] [files]...
	-h          show this help
	-t test     test names (multiple ok, default all 'test_*')
	-P path     prepend to package.path
	-C cpath    prepend to package.cpath
]])
	os.exit(1)
end

local function argi(argv, i)
	return argv[i] or help()
end

local function args(argv)
	local out = { files={}, tests={} }
	local i = 1
	while i <= #argv do
		if argv[i] == "-h" then
			help()
		elseif argv[i] == "-t" then
			out.tests[argi(argv, i+1)], i = true, i+2
		elseif argv[i] == "-P" then
			out.path, i = argi(argv, i+1), i+2
		elseif argv[i] == "-C" then
			out.cpath, i = argi(argv, i+1), i+2
		elseif argv[i]:match("^%-") then
			-- ignore unknown args, let the shell script handle them
			i = i+1
		else
			out.files[#out.files+1], i = argv[i], i+1
		end
	end
	return out
end

local function main(argv)
	argv = args(argv)
	if #argv.files == 0 then lstestfiles(argv.files) end
	if argv.path then package.path = string.format("%s;%s", argv.path, package.path) end
	if argv.cpath then package.cpath = string.format("%s;%s", argv.cpath, package.cpath) end
	local tests = loadtests(argv.files)
	if next(argv.tests) then tests = filtertests(tests, argv.tests) end
	tap(tests)
end

main({...})
