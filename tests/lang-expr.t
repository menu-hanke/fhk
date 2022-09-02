-- vim: ft=lua:
local fhk = require "fhk"

function test_expr_fraction()
	local graph = fhk.graph(function()
		var "x" { function() return 1 end }
		var "y" { function() return 2 end }
		derive "z" {
			params "x y",
			impl.Expr "$1/$2"
		}
	end)
	local query = graph:query "z"
	graph:prepare()
	assert(query().z == 1/2)
end

function test_expr_multi()
	local graph = fhk.graph(function()
		model () {
			returns "x y",
			impl.Expr "1, 2"
		}
	end)
	local query = graph:query("x", "y")
	graph:prepare()
	local res = query()
	assert(res.x == 1 and res.y == 2)
end

function test_const_num()
	local graph = fhk.graph(function()
		derive "x" { impl.Expr(123) }
	end)
	local query = graph:query "x"
	graph:prepare()
	assert(query().x == 123)
end

function test_const_multi()
	local graph = fhk.graph(function()
		model () {
			returns "x y",
			impl.Expr(1, 2)
		}
	end)
	local query = graph:query("x", "y")
	graph:prepare()
	local res = query()
	assert(res.x == 1 and res.y == 2)
end

function test_const_broadcast()
	local graph = fhk.graph(function()
		var "g" { function() return fhk.space1(3) end }
		derive "g#x" { impl.Expr(1) }
	end)
	local query = graph:query "g#x"
	graph:prepare()
	local res = query()
	assert(res.g_x[0] == 1 and res.g_x[1] == 1 and res.g_x[2] == 1)
end
