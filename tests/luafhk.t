-- vim: ft=lua
local ffi = require "ffi"
local fhk = require "fhk"
local driver = require "fhk_driver"
local buffer = require "string.buffer"

test_decl = function()
	local decl = fhk.new(
		fhk.group("a",
			fhk.virtual("x", 1),
			fhk.shape(1)
		)
	)
	decl:graph(
		fhk.g.model(
			"a#m",
			"x" *fhk.g.as "double", "->", "y" *fhk.g.as "double",
			function(x) return x+1 end
		)
	)
	local solver = decl { "a#y", value=fhk.scalar() }
	decl:ready()
	local result = solver()
	assert(result.a_y == 2)
end

test_struct_view_bound = function()
	local struct = ffi.new("struct { double x; double y; }", 1, 2)
	local decl = fhk.new(
		fhk.group("a",
			fhk.struct(struct),
			fhk.shape(1)
		)
	)
	decl:graph(
		fhk.g.model(
			"a#mod",
			"x", "y", "->", {"z", "w"} *fhk.g.as "double",
			function(x, y) return x, y end
		)
	)
	local solver = decl { "a#z", "a#w", value=fhk.scalar() }
	decl:ready()
	local res = solver()
	assert(res.a_z == 1 and res.a_w == 2)
end

test_struct_view_unbound = function()
	local ct = ffi.typeof "struct { double x; double y; }"
	local decl = fhk.new(
		fhk.group("a",
			fhk.struct(ct, function(_, X) return X.struct end),
			fhk.shape(1)
		)
	)
	decl:graph(
		fhk.g.model(
			"a#mod",
			"x", "y", "->", {"z", "w"} *fhk.g.as "double",
			function(x, y) return x, y end
		)
	)
	local solver = decl { "a#z", "a#w", value=fhk.scalar() }
	decl:ready()
	local res = solver { struct = ct(1,2) }
	assert(res.a_z == 1 and res.a_w == 2)
end

test_array_view_bound = function()
	local xs = ffi.new "double[8]"
	for i=0, 7 do
		xs[i] = i
	end
	local decl = fhk.new(
		fhk.group("a",
			fhk.named("x", fhk.array(xs, fhk.c.interval1(0, 8))),
			fhk.shape(8)
		)
	)
	local solver = decl { "a#x", value=fhk.vector(8) }
	decl:ready()
	local res = solver()
	for i=0, 7 do
		assert(res.a_x[i] == i)
	end
end

test_array_view_unbound = function()
	local xs = ffi.new "int[10]"
	for i=0, 9 do
		xs[i] = i*i
	end
	local decl = fhk.new(
		fhk.group("a",
			fhk.named("x", fhk.array("int", function() return xs, fhk.c.interval1(0, 10) end)),
			fhk.shape(10)
		)
	)
	local solver = decl { "a#x", value=fhk.vector(10) }
	decl:ready()
	local res = solver()
	for i=0, 9 do
		assert(res.a_x[i] == i*i)
	end
end

test_usermap = function()
	local decl = fhk.new(
		fhk.group("a",
			fhk.virtual("x", function(inst) return inst end),
			fhk.shape(4)
		),
		fhk.map(
			"umap(is):(is)",
			function(i) return (i+1)%4 end,
			function(j) return (j+3)%4 end
		)
	)
	decl:graph(
		fhk.g.model(
			"a#mod",
			"x" *fhk.g.as "double" *fhk.g.choose "umap",
			"->",
			"y" *fhk.g.as "double",
			function(x) return x end
		)
	)
	local solver = decl("a#y")
	decl:ready()
	local result = solver()
	assert(result.a_y[0] == 1 and result.a_y[1] == 2 and result.a_y[2] == 3 and result.a_y[3] == 0)
end

test_shape_func = function()
	local decl = fhk.new(
		fhk.group("a",
			fhk.virtual("x", function(inst) return inst end, "double"),
			fhk.shape(function() return 2 end)
		)
	)
	local solver = decl("a#x")
	decl:ready()
	local result = solver()
	assert(result.a_x[0] == 0 and result.a_x[1] == 1)
end

test_reuse_solver = function()
	local called = false
	local decl = fhk.new(fhk.group("a", fhk.shape(1)))
	decl:graph(
		fhk.g.model(
			"a#mod",
			"->", {"x", "y"} *fhk.g.as "double",
			function()
				assert(not called)
				called = true
				return 1, 2
			end
		)
	)
	local resx = decl { "a#x", value=fhk.scalar() }
	local resy = decl { "a#y", value=fhk.scalar() }
	decl:ready()
	local S, A = decl.init()
	local rx = resx(S)
	local ry = resy(S)
	assert(rx.a_x == 1)
	assert(ry.a_y == 2)
	A:destroy()
end

test_key = function()
	local decl = fhk.new(
		fhk.group("a",
			fhk.virtual("x", function(inst, X) return X.values[inst] end, "double"),
			fhk.shape(4)
		)
	)
	local solver = decl { "a#x", subset=fhk.key("ss"), value=fhk.key("buf") }
	decl:ready()
	local ss, _anchor1 = fhk.c.tosubset { 0, 2 }
	local buf = ffi.new("double[2]")
	solver {
		values = { [0]=3, [1]=1, [2]=4, [3]=1 },
		ss = ss,
		buf = buf
	}
	assert(buf[0] == 3 and buf[1] == 4)
end

test_gfile = function()
	local decl = fhk.new(
		fhk.group("a", fhk.virtual("x", 2, "double"), fhk.shape(1)),
		fhk.group("b", fhk.virtual("y", function(inst) return inst*inst end, "double"), fhk.shape(4)),
		fhk.map(
			"a->b(kv):(kv)",
			function() return fhk.c.interval1(0, 4) end,
			function() return fhk.c.unit(0) end
		)
	)
	decl:graph("example.g.lua")
	local solver = decl { "a#z", "a#w", value=fhk.scalar() }
	decl:ready()
	local res = solver()
	assert(
		res.a_z == 0 + 1 + 4 + 9
		and res.a_w == 2 * (0 + 1 + 4 + 9)
	)
end

test_gcheck = function()
	local decl = fhk.new(
		fhk.group("a",
			fhk.virtual("u8", 1, "uint8_t"),
			fhk.virtual("f64", 10, "double"),
			fhk.shape(1)
		)
	)
	decl:graph(function()
		model "a#mod1" {
			cost { k = 0 },
			check "u8" *is {4,5,6},
			returns "x" *as "double",
			impl.Lua(function() return 1 end)
		}
		model "a#mod2" {
			cost { k = 10 },
			check "u8" *is {0,1,2},
			check "f64" *ge(5),
			returns "x" *as "double",
			impl.Lua(function() return 2 end)
		}
		model "a#mod3" {
			cost { k = 100 },
			returns "x" *as "double",
			impl.Lua(function() return 3 end)
		}
	end)
	local solver = decl { "a#x", value=fhk.scalar() }
	decl:ready()
	local res = solver()
	assert(res.a_x == 2)
end

test_label = function()
	local decl = fhk.new(
		fhk.group("a", fhk.virtual("x", 1, "uint8_t"), fhk.shape(1)),
		fhk.label { a=1, b=2 }
	)
	decl:graph(function()
		model "a#mod" {
			check "x" *is { "a", "b" },
			returns "y" *as "double",
			impl.Lua(function() return 1 end)
		}
	end)
	local solver = decl { "a#y", value=fhk.scalar() }
	decl:ready()
	local res = solver()
	assert(res.a_y == 1)
end

test_derive = function()
	local decl = fhk.new(fhk.group("a", fhk.virtual("x", 1, "double"), fhk.shape(1)))
	decl:graph(function()
		derive ("a#y" *as "double") {
			params "x",
			impl.Lua(function(x) return x+1 end)
		}
	end)
	local solver = decl { "a#y", value=fhk.scalar() }
	decl:ready()
	local res = solver()
	assert(res.a_y == 2)
end

test_modcall_const = function()
	local decl = fhk.new(
		fhk.group("a", fhk.shape(1)),
		fhk.group("b", fhk.shape(3))
	)
	decl:graph(
		fhk.g.model(
			"a#return-scalars",
			"->", {"x","y"} *fhk.g.as "double",
			fhk.g.impl.Const(1)
		),
		fhk.g.model(
			"a#broadcast-scalars",
			"->", {"b#x","b#y"} *fhk.g.as "int" *fhk.g.choose "space",
			fhk.g.impl.Const({2,3})
		)
	)
	local solver = decl(
		{ "a#x", "a#y", value=fhk.scalar() },
		{ "b#x", "b#y" }
	)
	decl:ready()
	local res = solver()
	assert(
		res.a_x == 1
		and res.a_y == 1
		and res.b_x[0] == 2 and res.b_x[1] == 2 and res.b_x[2] == 2
		and res.b_y[0] == 3 and res.b_y[1] == 3 and res.b_y[2] == 3
	)
end

test_custom_opcode = function()
	local gtab = { ["a#x"] = ffi.new("double[1]", 123) }
	local decl = fhk.new(
		fhk.group("a",
			fhk.tagged("var", function(_, event)
				if gtab[event.name] then
					event.setcts("double")
					event.setjfunc(function(fb)
						fb.upv.g = gtab
						fb.src:putf("C.fhk_setvalue(S, D.idx, D.inst, g['%s']+D.inst)", event.name)
					end)
				end
			end),
			fhk.shape(1)
		)
	)
	local solver = decl { "a#x", value=fhk.scalar() }
	decl:ready()
	local result = solver()
	assert(result.a_x == 123)
end

test_trap_model = function()
	local decl = fhk.new(fhk.group("a", fhk.virtual("y", 1, "double"), fhk.shape(1)))
	decl:graph(
		fhk.g.model("a#mody", "y", "->", "x" *fhk.g.as "double", function(y) return y end),
		fhk.g.model("a#modz", "z", "->", "x" *fhk.g.as "double", function(z) return z end)
	)
	local solver = decl { "a#x", value=fhk.scalar() }
	decl:ready()
	local result = solver()
	assert(result.a_x == 1)
end

-- TODO: implement this api.
--test_inspect = function()
--	local decl = fhk.decl.create(
--		fhk.view.group("a",
--			fhk.view.virtual("y", 1, "double"),
--			fhk.view.shape(1)
--		),
--		fhk.view.model(
--			"a#mod",
--			"y", "->", fhk.g.as("x", "double"),
--			fhk.g.cost { k=100 },
--			function(y) return y end
--		)
--	)
--	local newsolver = fhk.decl.make_solver(decl)
--	local solver = decl { "a#x", value=fhk.result.scalar() }
--	fhk.decl.materialize(decl)
--	local S = newsolver()
--	solver(S)
--
--	-- layout puts given variables first, so y is determinitistically layouted as 0.
--	local y0 = fhk.debug.inspect(S, "obj", 0, 0)
--	assert(y0.what == "given" and y0.ptr)
--
--	-- we don't test E, the solver may clear it after setting C and/or V.
--	-- this is an implementation detail.
--
--	local x0 = fhk.debug.inspect(S, "obj", 1, 0)
--	assert(
--		x0.what == "computed"
--		and x0.c and x0.v and x0.ptr
--		and x0.edge == 0 and x0.inst == 0
--		and x0.cost == 100
--	)
--
--	local mod0 = fhk.debug.inspect(S, "obj", -1, 0)
--	assert(
--		mod0.what == "model"
--		and mod0.c and mod0.v
--		and mod0.cost == 100
--	)
--end

test_hook = function()
	local buf = buffer.new()
	local c = {group="g", map="u", var="v", model="m"}
	local decl = fhk.new(
		fhk.group("a", fhk.virtual("x", 1, "double"), fhk.shape(1)),
		fhk.map("map(is):(is)", function() return 0 end, function() return 0 end),
		fhk.tagged("emit.pre", function(_, event)
			driver.hook(event.fb, {f=function() buf:put(c[event.obj.tag]) end})
		end),
		fhk.tagged("emit.post", function(_, event)
			driver.hook(event.fb, {f=function() buf:put(c[event.obj.tag]:upper()) end})
		end)
	)
	decl:graph(
		fhk.g.model(
			"a#mod",
			"x" *fhk.g.choose "map",
			"->",
			"y" *fhk.g.choose "map" *fhk.g.as "double",
			function(x) return x end
		)
	)
	local solver = decl("a#y")
	decl:ready()
	solver()
	assert(tostring(buf) == "gGuUuUvVmM")
end

test_trap_no_chain = function()
	local decl = fhk.new(fhk.group("a", fhk.shape(1)))
	decl("a#x")
	assert(fails(function() decl:ready() end, "no chain with finite cost"))
end

test_missing_var = function()
	local decl = fhk.new()
	decl("a#x")
	assert(fails(function() decl:ready() end, "no chain with finite cost"))
end

test_missing_type_var = function()
	local decl = fhk.new(fhk.virtual("a#x"))
	decl("a#x")
	assert(fails(function() decl:ready() end, "non%-unique ctype"))
end

test_incompatible_type_var = function()
	local decl = fhk.new(fhk.virtual("a#x", 1, "double"))
	decl:graph(
		fhk.g.model(
			"a#mod1",
			fhk.g.check "x" *fhk.g.ge(0),
			"->",
			"y" *fhk.g.as "double",
			function() end
		),
		fhk.g.model(
			"a#mod2",
			fhk.g.check "x" *fhk.g.le(0),
			"->",
			"y" *fhk.g.as "int",
			function() end
		)
	)
	decl("a#y")
	assert(fails(function() decl:ready() end, "non%-unique ctype"))
end

test_missing_shape = function()
	local decl = fhk.new(fhk.virtual("a#x", 0, "double"))
	decl("a#x")
	assert(fails(function() decl:ready() end, "group missing shape"))
end

test_missing_map = function()
	local decl = fhk.new(fhk.group("a", fhk.shape(1)))
	assert(
		fails(
			function()
				decl:graph(
					fhk.g.model(
						"a#mod",
						"->", "x" *fhk.g.choose "missing" *fhk.g.as "double",
						function() end
					)
				)
			end,
			"missing inverse"
		)
	)
end

test_no_chain = function()
	local decl = fhk.new(fhk.group("a", fhk.virtual("x", -1, "double"), fhk.shape(1)))
	decl:graph(
		fhk.g.model(
			"a#mod",
			"->", "y" *fhk.g.as "double",
			fhk.g.check "x" *fhk.g.ge(0),
			function() end
		)
	)
	local solver = decl("a#y")
	decl:ready()
	assert(fails(solver, "no chain with finite cost"))
end

test_view_conflict = function()
	local decl = fhk.new(
		fhk.virtual("a#x", 0, "double"),
		fhk.virtual("a#x", 1, "int")
	)
	assert(fails(function() decl("a#x") end, "inconsistent value"))
end

test_check_type_conflict = function()
	local decl = fhk.new(fhk.virtual("a#x", 0, "double"))
	decl:graph(
		fhk.g.model(
			"a#mod",
			fhk.g.check "x" *fhk.g.is {1},
			"->",
			"y" *fhk.g.as "double",
			function() end
		)
	)
	decl("a#y")
	assert(fails(function() decl:ready() end, "guard opcode.*is not applicable for ctype"))
end
