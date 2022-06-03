-- vim: ft=lua
-- fhk core tests.
local fhk = require "fhk"
local _ = require "testgraph"

-- identity : X^n -> X^n
local function id(...) return ... end

-- n-dimension dot product : X^n -> X^1
local function dot(...)
	local xs = {...}
	local d = 0

	for i,x in ipairs(xs[1]) do
		for j=2, #xs do
			x = x * xs[j][i]
		end
		d = d + x
	end

	return d
end

local function cf(...)
	local r = {...}
	return function() return unpack(r) end
end

---- smoke tests ----------------------------------------

test_solver_single = _(function()
	model { "a -> x", id }

	given { a = {123} }
	solution { x = {123} }
end)

test_solver_cost = _(function()
	model { "-> x %1", 2, k=2 }
	model { "-> x %2", 1, k=1 }

	solution { x = {1} }
end)

test_solver_given_check_pass = _(function()
	model { "-> x [a>=0+10]", 1 }
	model { "-> x [a<=0+10]", 2 }

	given { a = {1} }
	solution { x = {1} }
end)

test_solver_given_check_fail = _(function()
	model { "-> x [a>=0+10]", 1 }
	model { "-> x [a<=0+10]", 2 }

	given { a = {-1} }
	solution { x = {2} }
end)

test_solver_computed_check = _(function()
	model { "-> x", 1 }
	model { "-> y %k100", 1, k=100 }
	model { "-> y [x<=0+1000] %k1", 2, k=1 }

	solution { y = {1} }
end)

test_solver_chain = _(function()
	model { "a -> x", id }
	model { "x -> y", id }

	given { a = {123} }
	solution { x = {123} }
end)

test_solver_builtin_map = _(function()
	model { "g# a:space -> g#x", dot }

	given { a = {1, 2, 3} }
	solution { ["g#x"] = {1+2+3} }
end)

test_solver_complex_parameter = _(function()
	map2 {
		"even",
		forward = map("k", {0, 2}),
		inverse = map("i", function(i) return (i%2==0) and fhk.c.unit(i) or fhk.c.emptyset end)
	}

	model { "g# a:even -> g#x", dot }

	given { a = {1, na, 3, na} }
	solution { ["g#x"] = {1+3} }
end)

test_solver_set_chain = _(function()
	model { "default# a -> x", id }
	model { "g# x:space -> g#y", dot }

	given { a = {1, 2, 3} }
	solution { ["g#y"] = {1+2+3} }
end)

test_solver_ret_space = _(function()
	model { "-> x:space", cf {1, 2, 3} }

	solution { x = {1, 2, 3} }
end)

test_solver_ret_multi = _(function()
	model { "a,b -> z,w", id, k=1 }
	model { "c,d -> z,w", id, k=2 }

	given { a = {1, 2, 3}, b = {4, 5, 6} }
	solution { z = {1, 2, 3}, w = {4, 5, 6} }
end)

test_solver_offset_collect = _(function()
	model { "a -> x", id }

	given { a = {na, 2, 3} }
	solution { x = {na, 2, 3} }
end)

test_solver_modcall_emptyset = _(function()
	model { "g# a:space -> g#x", 1 }

	given { a = {} }
	solution { ["g#x"] = {1} }
end)

test_solver_set_given_constraint_pass = _(function()
	model { "default# ->x [g#a>=0:space+100]", 1 }
	model { "->x", 2, k=50 }

	given { ["g#a"] = {1, 1} }
	solution { x = {1} }
end)

test_solver_set_given_constraint_fail = _(function()
	model { "default# ->x [g#a>=0:space+100]", 1 }
	model { "->x", 2, k=50 }

	given { ["g#a"] = {1, -1} }
	solution { x = {2} }
end)

test_solver_set_computed_constraint_pass = _(function()
	model { "default# ->x [g#a>=0:space+100]", 1 }
	model { "->x", 2, k=50 }
	model { "g# g#a0->g#a", id }

	given { ["g#a0"] = {1, 1} }
	solution { x = {1} }
end)

test_solver_set_computed_constraint_fail = _(function()
	model { "default# ->x [g#a>=0:space+100]", 1 }
	model { "->x", 2, k=50 }
	model { "g# g#a0->g#a", id }

	given { ["g#a0"] = {1, -1} }
	solution { x = {2} }
end)

test_solver_set_computed_param = _(function()
	map2 {
		"first",
		forward = map("k", {0}),
		inverse = map("i", function(inst) return inst == 0 and fhk.c.unit(0) or fhk.c.emptyset end)
	}

	map2 {
		"second",
		forward = map("k", {1}),
		inverse = map("i", function(inst) return inst == 1 and fhk.c.unit(0) or fhk.c.emptyset end)
	}

	model { "default# ->g#a:first", cf{123} }
	model { "default# ->g#a:second", cf{456} }
	model { "default# g#a:second->x", function(x) return x[1] end }

	group { "g", shape=2 }

	solution { x = {456} }
end)

test_solver_no_chain_check = _(function()
	model { "->x [a>=0+200]", 1, k=1 }
	model { "->x", 2, k=100}
	model { "->a [b>=0+inf]", 10 }

	given { b = {-1} }
	solution { x = {2} }
end)

test_solver_umap_association = _(function()
	local data = {}
	local xs = {}

	local num = 20

	for j=1, num do
		map2 {
			string.format("umap%d_g", j),
			forward = map("k", {j-1}),
			inverse = map("i", function(inst) return inst == j-1 and fhk.c.unit(j-1) or fhk.c.emptyset end)
		}

		map2 {
			string.format("umap%d_default", j),
			forward = map("k", {j-1}),
			inverse = map("i", function(inst) return inst == j-1 and fhk.c.unit(j-1) or fhk.c.emptyset end)
		}

		model {
			string.format("h# g%d#x%d:umap%d_g->default#x:umap%d_default", j, j, j, j),
			id
		}

		data[j] = j
		xs[string.format("g%d#x%d", j, j)] = data
	end

	group { "h", shape=num }

	given(xs)
	solution { x = data }
end)

---- main loop tests ----------------------------------------

test_solver_bound_retry = _(function()
	model { "x->a",  1, k=1, c=1}
	model { "y->a",  2, k=2, c=2}
	model { "xp->x [xp>=0+100] [xq>=0+200]", 3  }
	model { "yp->y [yp>=0+100] [yq>=0+200]", 4  }
	model { "->xp",  -1 }
	model { "->xq",  1  }
	model { "->yp",  1  }
	model { "->yq",  -1 }

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

	solution { a = {1} }
end)

test_solver_lowbound_update = _(function()
	model { "->z [a>=0+100]", 1}
	model { "z->y", 1 }
	model { "y->x", 1 }
	model { "->x", 2, k=50 }

	-- solve x
	--     try y->x
	--         solve y
	--             try z->y
	--             fail, update z
	--         fail, update y
	--         (this asserts if y lowbound is too high)

	given { a={-1} }
	solution { x={2} }
end)

test_solver_merge_guard = _(function()
	var { "x", ctype="uint8_t" }
	model { "->y [x&1,2+inf]", 1 }
	model { "->z [x&2,1+inf]", 2 }
	given { x={1} }
	solution { y={1}, z={2} }
end)

---- evaluator tests ----------------------------------------

test_solver_return_overlap = _(function()
	model { "->x,y", cf(1, 1), k=1 }
	model { "->y,z", cf(2, 2), k=2 }
	model { "->x,z", cf(3, 3), k=3 }

	solution { x = {1}, y = {1}, z = {2} }
end)

test_complex_scatter = _(function()
	map2 {
		"complex",
		forward = map("k", {0, 2}),
		inverse = map("i", function(inst)
			return (inst == 0 or inst == 2) and fhk.c.unit(0) or fhk.c.emptyset
		end)
	}

	model { "g# ->x:complex", cf{123,456} }

	group { "g", shape=1 }
	solution { x = {123, na, 456} }
end)

test_commit_split_range = _(function()
	map2 {
		"range03",
		forward = map("k", {0,1,2,3}),
		inverse = map("i", function(inst) return inst <= 3 and fhk.c.unit(0) or fhk.c.emptyset end)
	}

	model { "g# -> x:range03", cf{1,1,1,1} }
	model { "g# -> x:space", k=10, cf{2,2,2,2, 2,2,2,2} }

	group { "g", shape=1 }
	solution { x = {1,1,1,1, 2,2,2,2}}
end)

test_complex_split_range = _(function()
	map2 {
		"complex",
		forward = map("k", {0,2,3}),
		inverse = map("i", function(inst)
			return (inst == 0 or inst == 2 or inst == 3) and fhk.c.unit(0) or fhk.c.emptyset
		end)
	}

	-- the check will force early evaluation of `x`,
	-- then when the better complex model is later evaluated,
	-- it must replace speculated values of `y` produced while evaluating `x`.

	model { "g# -> x:space,y:space", cf({0,1,2,3},{4,5,6,7}), k=10 }
	model { "g# -> z:space [x>=0:space+inf]", cf{0,0,0,0} }
	model { "-> y:complex", cf{-4,-6,-7} }

	group { "g", shape=1 }
	solution { y={-4,5,-6,-7}, z={0,0,0,0} }
end)

---- check/guard tests ----------------------------------------

test_scan_computed_block = _(function()
	-- solving the first y writes the bitmap,
	-- and next y scans the full computed bitmap.

	local x0 = {}
	for i=1, 100 do
		x0[i] = i
	end

	model { "x0 -> x", id }
	model { "x -> y1 [x>0+inf]", id }
	model { "x -> y2 [x>0+inf]", id }

	given { x0 = x0 }
	solution { y1 = x0, y2 = x0 }
end)

test_scan_given_block = _(function()
	-- same thing as `test_scan_computed_block`, but the scan variable is given here.

	local x = {}
	for i=1, 100 do
		x[i] = i
	end

	model { "x -> y1 [x>0+inf]", id }
	model { "x -> y2 [x>0+inf]", id }

	given { x = x }
	solution { y1 = x, y2 = x }
end)

test_scan_block_all_pass = _(function()
	-- one guard is evaluated one var at a time, the next one evaluates the whole
	-- space at once.
	-- this doesn't have separate computed/given versions, since it's supposed to test
	-- the evaluator function itself.

	local x = {}
	for i=1, 100 do
		x[i] = i
	end

	model { "x -> y1 [x>0+inf]", id }
	model { "x -> y2 [x>=0+inf]", id }

	given { x = x }
	solution { y1 = x, y2 = x }
end)

test_scan_block_mixed = _(function()
	-- same thing as `test_scan_block_all_pass`, but with half of the tests failing.
	-- also, we use a computed variable here, this is (should be) arbitrary.

	local x0, yplus, yminus = {}, {}, {}
	for i=1, 100 do
		if i%2 == 0 then
			x0[i], yplus[i], yminus[i] = i, i, na
		else
			x0[i], yplus[i], yminus[i] = -i, na, i
		end
	end

	model { "x0 -> x", id }
	model { "x -> yplus [x>=0+inf]", id }
	model { "x -> yminus [x<0+inf]", function(x) return -x end }

	given { x0 = x0 }
	solution { yplus = yplus, yminus = yminus }
end)

---- stress test ----------------------------------------

test_solver_stress_candidates = _(function()
	for i=1, 10 do
		model { string.format("->w%d", i), i, k=(i-1)/10 }
	end

	for i=1, 10 do
		-- min (i^2 - 10*i + 100 : i=1..10) = 75 (i = 5)
		model { string.format("->x%d", i), i, k=i^2, c=1 }
		model { string.format("->y%d", i), i, k=100-10*i, c=1 }

		for j=1, 10 do
			model {
				string.format("x%d,y%d,w%d->z", i, i, j),
				function(x, y, w) return 100*x + 10*y + w end
			}
		end
	end

	-- x5, y5, w1
	solution { z = { 551 } }
end)

test_solver_check_bitmap_over64 = _(function()
	local ws, xs = {}, {}

	for i=1, 100 do
		local v = i % 64
		ws[i] = v

		if v == 1 then                            xs[i] = 1
		elseif v == 2 or v == 3 or v == 4 then    xs[i] = 2
		elseif v == 15 or v == 16 or v == 17 then xs[i] = 3
		elseif v == 32 then                       xs[i] = 4
		elseif v == 63 then                       xs[i] = 5
		else                                      xs[i] = 0
		end
	end

	var { "w", ctype="uint8_t" }
	model { "->x[w&1+inf]",        1 }
	model { "->x[w&2,3,4+inf]",    2 }
	model { "->x[w&15,16,17+inf]", 3 }
	model { "->x[w&32+inf]",       4 }
	model { "->x[w&63+inf]",       5 }
	model { "->x", k=100,          0 }

	given { w = ws }
	solution { x = xs }
end)

---- error tests ----------------------------------------
-- TODO.

---- prune tests ----------------------------------------

test_prune_omit_model = _(function()
	model { "->x %1", k=1 }
	model { "->x %2", k=2 }

	pin { "x" }
	pruned { "x", "->x %1" }
end)

test_prune_pick_bound = _(function()
	model { "x->y [x>=0+100]" }
	model { "x->y", k=2 }
	model { "x->y [x>=0+100] %k3", k=3 }

	pin { "y" }
	pruned { "x", "y", "x->y [x>=0+100]", "x->y" }
end)

test_prune_separate_cycle = _(function()
	model { "x->y" }
	model { "y->x" }
	model { "x->z" }
	model { "->z" }

	pin { "z" }
	pruned { "z", "->z" }
end)

test_prune_infinite_model = _(function()
	model { "->y", k=math.huge }
	model { "y->z" }
	model { "x->z" }

	pin { "z" }
	pruned { "x", "z", "x->z" }
end)

test_prune_propagate_infinite_bound = _(function()
	model { "->y[x>=0+inf]" }
	model { "y->z" }

	pin { "z" }
	pruned { "x", "y", "z", "->y[x>=0+inf]", "y->z" }
end)

test_prune_propagate_usermap_return_bound = _(function()
	map2 {
		"umap",
		forward = map("k", {0}),
		inverse = map("k", {0})
	}

	model { "->y:umap", k=0 }
	model { "->y", k=100 }

	pin { "y" }
	pruned { "y", "->y:umap", "->y" }
end)

test_prune_propagate_usermap_param_bound = _(function()
	map2 {
		"umap",
		forward = map("k", {0}),
		inverse = map("k", {0})
	}

	model { "->x", k=100 }
	model { "x:umap->y" }
	model { "->y", k=10 }
	model { "y->z" }
	model { "->z", k=5 }

	pin { "z" }

	-- TOOD: this is what the current algorithm should return, however maybe in the future
	-- it should also take into account the beta bound like the solver that, then it could
	-- also prune "->y".
	-- this probably doesn't have much of an impact in real-world graphs, but it would be a nice
	-- property.
	pruned { "x", "y", "z", "->x", "->y", "x:umap->y", "y->z", "->z" }
end)

test_prune_retain_uncomputable_umap = _(function()
	map2 {
		"umap",
		forward = map("k", {0}),
		inverse = map("k", {0})
	}

	model { "->x", k=math.huge }
	model { "x->y" }
	model { "y:umap->z" }

	pin { "z" }

	pruned { "x", "y", "z", "->x", "x->y", "y:umap->z" }
end)

test_prune_omit_high_cycle = _(function()
	model { "x->y", k=100}
	model { "y->x", k=1 }
	model { "x->z", k=1 }
	model { "y->z", k=1 }
	model { "->x",  k=100}
	model { "->y",  k=1 }

	pin { "z" }
	pruned { "y", "z", "y->z", "->y" }
end)

test_prune_retain_bounded_cycle = _(function()
	model { "x->y" }
	model { "y->x" }
	model { "x->z" }
	model { "y->z" }
	model { "->x [w>=0+100]" }
	model { "->y [w<=0+100]" }

	pin { "z" }
	pruned {
		"x", "y", "z", "w",
		"x->y", "y->x", "x->z", "y->z", "->x [w>=0+100]", "->y [w<=0+100]"
	}
end)

test_prune_stress_heap = _(function()
	for i=1, 100 do
		model { string.format("->x%d", i), k=i, c=1 }
		model { string.format("x%d->x", i), k=200-2*i, c=1 }
	end

	-- min (i + 200-2*i : i=1..100) = 100  (i=100)

	pin { "x" }
	pruned { "x", "x100", "->x100", "x100->x" }
end)
