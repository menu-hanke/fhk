-- vim: ft=lua
-- fhk solver tests.
local fhk = require "fhk"
local t = require "testlib"

local function id(...) return ... end
local function const(...)
	local v = {...}
	return function() return unpack(v) end
end

local function sum(...)
	local s = 0
	for _,t in ipairs({...}) do
		if type(t) == "table" then
			for _,v in ipairs(t) do
				s = s+v
			end
		else
			s = s+t
		end
	end
	return s
end

---- algorithm tests ----------------------------------------

test_solve_simple = t.g(function()
	var "x" { const(123) }
	derive "r" {
		params "x",
		id
	}
	----------------------------------------
	solution { r = 123 }
end)

test_solve_chain = t.g(function()
	derive "x" { const(1) }
	derive "y" { const(2) }
	derive "r" {
		params "x y",
		function(x, y) return x+y end
	}
	----------------------------------------
	solution { r = 1+2 }
end)

test_solve_given_checks = t.g(function()
	var "x+" { const(1) }
	var "x-" { const(-1) }
	derive "yok" {
		check "x+" *ge(0),
		const(0)
	}
	derive "yfail" {
		check "x-" *ge(0),
		const(0)
	}
	----------------------------------------
	solution { yok = 0 }
	solution { yfail = any } :fails "no chain with finite cost"
end)

test_solve_given_kmapg = t.g(function()
	var "m" { const(fhk.space1(5)) }
	var "m#x" { id }
	----------------------------------------
	solution { ["m#x"] = {0, 1, 2, 3, 4} }
end)

test_solve_given_kmapd = t.g(function()
	derive "m" { const(fhk.space1(5)) }
	var "m#x" { id }
	----------------------------------------
	solution { ["m#x"] = {0, 1, 2, 3, 4} }
end)

test_solve_chain_imapg = t.g(function()
	var "g" { const(fhk.space1(3)) }
	var "g#map" { function(j) return (j+1)%3 end, mode "s" }
	var "g#x" { id }
	derive "g#y" {
		params "x ~map",
		id
	}
	----------------------------------------
	solution { ["g#y"] = {1, 2, 0} }
end)

test_solve_pruned_computed_var = t.g(function()
	model () { returns "x", const(1), cost {k=1, c=1} }
	model () { returns "x", const(2), cost {k=2, c=1} }
	----------------------------------------
	solution { x = 1 }
end)

test_solve_computed_var_chain = t.g(function()
	var "x" { const(1) }
	derive "y" {
		check "x" *ge(0),
		const(1)
	}
	derive "y" {
		check "x" *le(0),
		const(2)
	}
	----------------------------------------
	solution { y = 1 }
end)

test_solve_var_heap = t.g(function()
	var "x" { const(3) }
	model "k1" {
		returns "y",
		check "x" *is { 1 },
		const(10),
		cost { k=1, c=1 }
	}
	model "k2" {
		returns "y",
		check "x" *is { 2 },
		const(20),
		cost { k=2, c=1 }
	}
	model "k3" {
		returns "y",
		check "x" *is { 3 },
		const(30),
		cost { k=3, c=1 }
	}
	model "k4" {
		returns "y",
		check "x" *is { 4 },
		const(40),
		cost { k=4, c=1 }
	}
	----------------------------------------
	solution { y=30 }
end)

test_solve_var_heap_reenter = t.g(function()
	var "w" { const(1) }
	derive "x1" {
		check "w" *is { 2 } *penalty(100),
		const(1)
	}
	derive "x2" {
		check "w" *is { 2 },
		const(2)
	}
	derive "x3" {
		check "w" *is { 3 },
		const(3)
	}
	model "y.1" {
		params "x1",
		returns "y",
		check "w" *is { 1 },
		cost { k=1, c=1 },
		id
	}
	model "y.2" {
		params "x2",
		returns "y",
		cost { k=2, c=1 },
		id
	}
	model "y.3" {
		params "x3",
		returns "y",
		cost { k=3, c=1 },
		id
	}
	----------------------------------------
	solution { y=1 }
end)

test_solve_bound_retry = t.g(function()
	derive "a" {
		params "x",
		const(1),
		cost {k=1, c=1}
	}
	derive "a" {
		params "y",
		const(2),
		cost {k=2, c=2}
	}
	derive "x" {
		params "xp",
		check "xp" *ge(0) *penalty(100),
		check "xq" *ge(0) *penalty(200),
		const(3)
	}
	derive "y" {
		params "yp",
		check "yp" *ge(0) *penalty(100),
		check "yq" *ge(0) *penalty(200),
		const(4)
	}
	derive "xp" { const(-1) }
	derive "xq" { const(1) }
	derive "yp" { const(1) }
	derive "yq" { const(-1) }
	----------------------------------------
	-- solve a
	--     try x->a
	--         solve x
	--             try xp->x
	--                 solve xp
	--                     try ->xp
	--                     xp = -1
	--                 beta bound
	--             beta bound
	--         beta bound
	--     beta bound
	--     try y->a
	--         solve y
	--             try yp->y
	--                 solve yp
	--                     try ->yp
	--                     yp = 1
	--                 solve yq
	--                     try ->yq
	--                     yq = -1
	--                 beta bound
	--             beta bound
	--         beta bound
	--     beta bound
	--     try x->a
	--         solve x
	--             try xp->x
	--                 solve xq
	--                     xq = 1
	--              x = 3
	--     a = 1
	----------------------------------------
	solution { a=1 }
end)

test_solve_collect_given_params = t.g(function()
	var "interval" { const(fhk.tosubset{1,2,3}) }
	var "complex" { const(fhk.tosubset{1,2,4,5}) }
	var "g" { const(fhk.space1(10)) }
	var "g#x" { id }
	derive "y" {
		params [[
			g#x ~interval
			g#x ~complex
		]],
		function(i, c)
			return sum(i) + 10*sum(c)
		end
	}
	----------------------------------------
	solution { y=(1+2+3)+10*(1+2+4+5) }
end)

test_solve_collect_computed_params = t.g(function()
	var "interval" { const(fhk.tosubset{3,4,5,6}) }
	var "complex" { const(fhk.tosubset{0,1,5,8,9}) }
	var "g" { const(fhk.space1(10)) }
	model "getx" {
		returns "g#x ~*",
		function()
			return {0,1,2,3,4,5,6,7,8,9}
		end
	}
	derive "y" {
		params [[
			g#x ~interval
			g#x ~complex
		]],
		function(i, c)
			return sum(i) + 10*sum(c)
		end
	}
	----------------------------------------
	solution { y=(3+4+5+6)+10*(0+1+5+8+9) }
end)

test_solve_overwrite_speculate = t.g(function()
	model () {
		cost { k=100, c=1 },
		returns "x y",
		const(1, 2)
	}
	model () {
		returns "x",
		const(3)
	}
	----------------------------------------
	solution { y=2 }
	solution { x=3 } -- solve after y for speculation.
end)

test_solve_eval_computed_speculate = t.g(function()
	model () {
		returns "x w",
		const(1, 2)
	}
	model () {
		check "w" *ge(0),
		returns "y",
		const(1)
	}
	model () {
		check "x" *ge(0),
		params "y",
		returns "z",
		const(1)
	}
	----------------------------------------
	solution { z=1 }
end)

test_solve_multi_instance_candidate = t.g(function()
	var "g" { const(fhk.space1(3)) }
	var "g#x" { ctype "uint8_t", id }
	model "g#m" {
		params "x",
		returns "global#y",
		check "x" *is {1},
		id
	}
	----------------------------------------
	solution { y=1 }
end)

test_solve_tolerance = t.g(function()
	derive "x" {
		cost {k=1/18, c=1},
		const(0)
	}
	derive "y" {
		params "x",
		check "x" *ge(0),
		cost {k=0, c=1.1},
		const(1)
	}
	derive "y" {
		params "x",
		check "x" *ge(0),
		cost {k=0, c=1.1},
		const(1)
	}
	----------------------------------------
	solution { y=1 }
end)

test_solve_writeback_interval = t.g(function()
	var "g" { const(fhk.space1(3)) }
	var "const1" { const(1), mode "s" }
	model "->y1" {
		returns "g#y ~const1",
		returns "z",
		const(10, 0)
	}
	model "->yall" {
		returns "g#y ~*",
		params "z", -- this is just to force `->y1` to be evaluated before this model
		cost {k=100, c=1},
		const{1,2,3}
	}
	derive "x" {
		params "g#y ~const1",
		id
	}
	----------------------------------------
	solution { ["g#y"]={1, 10, 3} }
end)

test_solve_writeback_complex = t.g(function()
	var "complex" { const(fhk.tosubset{0,1, 3,4,5, 8, 10}) }
	var "g" { const(fhk.space1(11)) }
	model "->x.complex" {
		returns "g#x ~complex",
		const({-1, -2, -3, -4, -5, -6, -7})
	}
	model "g#x.default" {
		cost {k=100, c=1},
		returns "x",
		const(0)
	}
	----------------------------------------
	solution { ["g#x"] = {-1,-2,0,-3,-4,-5,0,0,-6,0,-7} }
end)

test_solve_unused_return = t.g(function()
	model () {
		returns "x y",
		const(1, 2)
	}
	----------------------------------------
	solution { x=1 }
end)

---- "large" values ----------------------------------------

test_solve_large_graph = t.g(function()
	var "v0" { const(0) }
	for i=1, 1000 do
		derive ("v"..i) {
			params ("v"..(i-1)),
			function(x) return x+1 end
		}
	end
	----------------------------------------
	solution { v1000 = 1000 }
end)

test_solve_large_bitmaps = t.g(function()
	var "g" { const(fhk.space1(10000)) }
	var "g#b" { ctype "uint8_t", function(j) return j%4 end }
	model () {
		returns "g#x",
		cost {k=100, c=1},
		const(0)
	}
	derive "g#x" {
		check "b" *is {1,2},
		const(1)
	}
	derive "s" {
		params "g#x ~*",
		sum
	}
	----------------------------------------
	solution { s = 5000 }
end)

test_solve_stress_candidates = t.g(function()
	var "k" { const(6.5) }
	for i=1, 10 do
		derive ("w"..i) {
			const(i),
			check "k" *ge(i),
			cost { k=i/10, c=1 }
		}
		derive ("x"..i) {
			const(i),
			check "k" *le(i),
			cost { k=i^2, c=1 }
		}
		derive ("y"..i) {
			const(i),
			check "k" *le(i),
			cost { k=100-10*i, c=1 }
		}
		for j=1, 10 do
			derive "z" {
				params { "x"..i, "y"..i, "w"..j },
				function(x, y, w) return 100*x + 10*y + w end
			}
		end
	end
	----------------------------------------
	-- min (i^2 - 10*i + 100 : i=7..10) = 79 (i = 7)
	-- x5, y5, w1
	solution { z = 771 }
end)

test_solve_large_bound_heap = t.g(function()
	for i=1, 1000 do
		var ("x"..i) { function() return i end }
	end
	for j=1, 100 do
		derive ("y"..j) {
			params {
				"x"..((j-1)*10)+1,
				"x"..((j-1)*10)+2,
				"x"..((j-1)*10)+3,
				"x"..((j-1)*10)+4,
				"x"..((j-1)*10)+5,
				"x"..((j-1)*10)+6,
				"x"..((j-1)*10)+7,
				"x"..((j-1)*10)+8,
				"x"..((j-1)*10)+9,
				"x"..((j-1)*10)+10,
			},
			sum
		}
	end
	for k=1, 10 do
		derive ("z"..k) {
			params {
				"y"..((k-1)*10)+1,
				"y"..((k-1)*10)+2,
				"y"..((k-1)*10)+3,
				"y"..((k-1)*10)+4,
				"y"..((k-1)*10)+5,
				"y"..((k-1)*10)+6,
				"y"..((k-1)*10)+7,
				"y"..((k-1)*10)+8,
				"y"..((k-1)*10)+9,
				"y"..((k-1)*10)+10,
			},
			sum
		}
	end
	derive "w" {
		params "z1 z2 z3 z4 z5 z6 z7 z8 z9 z10",
		sum
	}
	----------------------------------------
	solution { w = 500500 }
end)

---- edge cases ----------------------------------------

test_solve_bitmap63_64_65 = t.g(function()
	for i=63, 65 do
		var ("g"..i) { function() return fhk.space1(i) end }
		var ("g"..i.."#b") { ctype "uint8_t", function(j) return j%2 end }
		model () {
			returns ("g"..i.."#x"),
			cost {k=100, c=1},
			const(0)
		}
		derive ("g"..i.."#x") {
			check "b" *is {0},
			const(1)
		}
		derive ("s"..i) {
			params ("g"..i.."#x ~*"),
			sum
		}
	end
	----------------------------------------
	solution { s63 = 32, s64 = 32, s65 = 33 }
end)

---- bugs found in the wild ----------------------------------------

test_solve_update_exit_cost = t.g(function()
	var "k1" { const(-1) }
	var "k2" {  const(-1) }
	model () {
		check "k1" *ge(0),
		returns "x",
		const(0)
	}
	model () {
		cost {k=100, c=1},
		returns "x",
		const(1)
	}
	model () {
		params "x",
		returns "y",
		check "k1" *le(0),
		function(x) return x+1 end
	}
	model () {
		returns "y",
		check "k2" *ge(0),
		cost {k=10, c=1},
		const(-1)
	}
	----------------------------------------
	solution { y=2 }
end)
