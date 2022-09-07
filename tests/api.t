-- vim: ft=lua
-- fhk lua api tests.
local fhk = require "fhk"
local ffi = require "ffi"

function test_api_graph()
	local g = fhk.graph(function()
		var "x" {
			function() return 1 end
		}
		model "m" {
			params "x",
			returns "y",
			function(x) return x+1 end
		}
	end)
	local q = g:query "y"
	g:prepare()
	assert(q().y == 2)
end

function test_api_struct_view_bound()
	local struct = ffi.new("struct { double x; double y; }", 1, 2)
	local graph = fhk.graph(function()
		var(fhk.struct(struct))
		model () {
			params "x y",
			returns "z w",
			function(x, y) return y, x end
		}
	end)
	local query = graph:query("z", "w")
	graph:prepare()
	local res = query()
	assert(res.z == 2 and res.w == 1)
end

function test_api_struct_view_unbound()
	local ct = ffi.typeof "struct { double x; double y; }"
	local graph = fhk.graph(function()
		var(fhk.struct(ct, function(_, X) return X.struct end))
		model () {
			params "x y",
			returns "z w",
			function(x, y) return y, x end
		}
	end)
	local query = graph:query("z", "w")
	graph:prepare()
	local res = query { struct = ct(1, 2) }
	assert(res.z == 2 and res.w == 1)
end

function test_api_array_view_bound()
	local xs = ffi.new "double[8]"
	for i=0, 7 do xs[i] = i end
	local graph = fhk.graph(function()
		var "a" { function() return fhk.space1(8) end }
		var "a#x" { fhk.array(xs, fhk.space1(8)) }
	end)
	local query = graph:query "a#x"
	graph:prepare()
	local res = query()
	for i=0, 7 do
		assert(res.a_x[i] == i)
	end
end

function test_api_array_view_unbound()
	local xs = ffi.new "int[10]"
	for i=0, 9 do xs[i] = i*i end
	local graph = fhk.graph(function()
		var "a" { function() return fhk.space1(10) end }
		var "a#x" { fhk.array("int", function() return xs, fhk.space1(10) end) }
	end)
	local query = graph:query "a#x"
	graph:prepare()
	local res = query()
	for i=0, 9 do
		assert(res.a_x[i] == i*i)
	end
end

function test_api_reuse_solver()
	local called = false
	local graph = fhk.graph(function()
		model () {
			returns "x y",
			function()
				assert(not called)
				called = true
				return 1, 2
			end
		}
	end)
	local qx = graph:query "x"
	local qy = graph:query "y"
	local G = graph:prepare()
	local mem = fhk.mem()
	local solver = fhk.solver(mem, G)
	local rx = qx(solver)
	local ry = qy(solver)
	assert(rx.x == 1)
	assert(ry.y == 2)
	mem:destroy()
end

function test_api_readkey()
	local graph = fhk.graph(function()
		var "a" { function() return fhk.space1(4) end }
		var "a#x" { function(i, X) return X.values[i] end }
	end)
	local query = graph:query { "a#x", subset=fhk.key("ss"), value=fhk.key("buf") }
	graph:prepare()
	local ss, _anchor = fhk.tosubset { 0, 2 }
	local buf = ffi.new("double[2]")
	query {
		values = { [0]=3, [1]=1, [2]=4, [3]=1 },
		ss = ss,
		buf = buf
	}
	assert(buf[0] == 3 and buf[1] == 4)
end

function test_api_gfile()
	local graph = fhk.graph(
		"example.g.lua",
		function()
			var "x" { function() return 2 end }
			var "b" { function() return fhk.space1(4) end }
			var "b#y" { function(i) return i*i end }
			var "m" { function() return fhk.space1(4) end }
		end
	)
	local query = graph:query("z", "w")
	graph:prepare()
	local res = query()
	assert(
		res.z == 0 + 1 + 4 + 9
		and res.w == 2 * (0 + 1 + 4 + 9)
	)
end

function test_api_gcheck()
	local graph = fhk.graph(function()
		var "u8" { function() return 1 end }
		var "f64" { function() return 10 end }
		model () {
			cost { k=0, c=1 },
			check "u8" *is {4,5,6},
			returns "x",
			function() return 1 end
		}
		model () {
			cost { k=10, c=1 },
			check "u8" *is {0,1,2},
			check "f64" *ge(5),
			returns "x",
			function() return 2 end
		}
		model () {
			cost { k=100, c=1 },
			returns "x",
			function() return 3 end
		}
	end)
	local query = graph:query "x"
	graph:prepare()
	local res = query()
	assert(res.x == 2)
end

function test_api_label()
	local graph = fhk.graph(function()
		var "x" { function() return 1 end }
		label { a=1, b=2 }
		model () {
			check "x" *is { "a", "b" },
			returns "y",
			function() return 1 end
		}
	end)
	local query = graph:query "y"
	graph:prepare()
	local res = query()
	assert(res.y == 1)
end

function test_api_derive()
	local graph = fhk.graph(function()
		var "x" { function() return 1 end }
		derive "y" {
			params "x",
			function(x) return x+1 end
		}
	end)
	local query = graph:query "y"
	graph:prepare()
	local res = query()
	assert(res.y == 2)
end

function test_api_skip_given_model()
	local graph = fhk.graph(function()
		var "x" { function() return 1 end }
		model () {
			returns "x",
			function() return 2 end
		}
	end)
	local query = graph:query "x"
	graph:prepare()
	local res = query()
	assert(res.x == 1)
end

function test_api_autocomplete_inverse_return()
	local graph = fhk.graph(function()
		var "g" { function() return fhk.space1(4) end }
		var "m" { function() return fhk.tosubset{1,3} end }
		model () {
			cost {k=100, c=1},
			returns "g#x",
			function() return 0 end
		}
		model "mod" {
			returns "g#x ~m",
			function() return {100, 200} end
		}
	end)
	local query = graph:query "g#x"
	graph:prepare()
	local res = query()
	assert(res.g_x[0] == 0 and res.g_x[1] == 100 and res.g_x[2] == 0 and res.g_x[3] == 200)
end

function test_api_autocomplete_inverse_explicit()
	local graph = fhk.graph(function()
		var "g" { function() return fhk.space1(4) end }
		var "g#m" {
			inverse "g#i",
			function(j) return (j+1)%4 end
		}
		var "g#i" { mode "s" }
		var "g#x" { function(j) return j*j end }
		derive "g#y" {
			params "x ~i",
			function(xi) return -xi end
		}
	end)
	local query = graph:query "g#y"
	graph:prepare()
	local res = query()
	assert(res.g_y[0] == -9 and res.g_y[1] == 0 and res.g_y[2] == -1 and res.g_y[3] == -4)
end

function test_api_autocomplete_inverse_implicit()
	local graph = fhk.graph(function()
		var "g" { function() return fhk.space1(3) end }
		var "g#->global" { function() return 0 end }
		model "m" {
			returns "g#x",
			function() return {1,2,3} end
		}
	end)
	local query = graph:query "g#x"
	graph:prepare()
	local res = query()
	assert(res.g_x[0] == 1 and res.g_x[1] == 2 and res.g_x[2] == 3)
end

function test_api_blacklist_missing_given()
	local graph = fhk.graph(function()
		var "y" { function() return 1 end }
		model () {
			params "y",
			returns "x",
			function(y) return y end
		}
		model () {
			params "z",
			returns "x",
			function(z) return z end
		}
	end)
	local query = graph:query "x"
	graph:prepare()
	local result = query()
	assert(result.x == 1)
end

function test_api_blacklist_missing_map()
	local graph = fhk.graph(function()
		var "x" { function() return 1 end }
		model () {
			params "x ~missing",
			returns "y",
			function(x) return x end
		}
		model () {
			params "x",
			returns "y",
			function(x) return -x end,
			cost {k=100,c=1}
		}
	end)
	local query = graph:query "y"
	graph:prepare()
	local result = query()
	assert(result.y == -1)
end

function test_api_sethook()
	local graph = fhk.graph(function()
		var "x" { function() return 1 end }
	end)
	local precalled, postcalled = 0, 0
	graph:sethook(
		function()
			precalled = precalled+1
			return function()
				postcalled = postcalled+1
			end
		end
	)
	local query = graph:query "x"
	graph:prepare()
	query()
	assert(precalled == 1 and postcalled == 1)
end

function test_api_no_chain()
	local graph = fhk.graph()
	graph:query "x"
	assert(fails(function() graph:prepare() end, "object is skipped"))
end

function test_api_no_ctype()
	local graph = fhk.graph(function()
		var "x" {
			ctype "double",
			ctype "int",
			function() return 0 end
		}
	end)
	graph:query "x"
	assert(fails(function() graph:prepare() end, "no possible ctype"))
end

function test_api_incompatible_ctype()
	local graph = fhk.graph(function()
		var "x" { function() return 0 end }
		model () {
			check "x" *ge(0),
			returns "y" *as "double",
			function() end
		}
		model () {
			check "x" *le(0),
			returns "y" *as "int",
			function() end
		}
	end)
	graph:query "y"
	assert(fails(function() graph:prepare() end, "no possible ctype"))
end

function test_api_runtime_no_chain()
	local graph = fhk.graph(function()
		var "x" { function() return -1 end }
		model () {
			check "x" *ge(0),
			returns "y",
			function() end
		}
	end)
	local query = graph:query "y"
	graph:prepare()
	assert(fails(query, "no chain with finite cost"))
end

function test_api_guard_ctype_conflict()
	local graph = fhk.graph(function()
		var "x" { ctype "double", function() return 0 end }
		model () {
			check "x" *is {1},
			returns "y" *as "double",
			function() end
		}
	end)
	graph:query "y"
	assert(fails(function() graph:prepare() end, "no possible ctype"))
end
