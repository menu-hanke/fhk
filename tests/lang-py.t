-- vim: ft=lua:
local fhk = require "fhk"
local ffi = require "ffi"

test_call_py_unannotated = function()
	local decl = fhk.new(fhk.group("a", fhk.virtual("x", 1), fhk.shape(1)))
	decl:graph(
		fhk.g.model(
			"a#m", "x" *fhk.g.as "double", "->", "y" *fhk.g.as "double",
			fhk.g.impl.Python("models", "ident_unannotated")
		)
	)
	local solver = decl { "a#y", value=fhk.scalar() }
	decl:ready()
	local result = solver()
	assert(result.a_y == 1)
end

test_call_py_annotated_scalar = function()
	local decl = fhk.new(fhk.group("a", fhk.virtual("x", 1), fhk.shape(1)))
	decl:graph(
		fhk.g.model(
			"a#m", "x" *fhk.g.as "double", "->", "y" *fhk.g.as "int",
			fhk.g.impl.Python("models", "ident_conv_annotated")
		)
	)
	local solver = decl { "a#y", value=fhk.scalar() }
	decl:ready()
	local result = solver()
	assert(result.a_y == 1)
end

test_call_py_memoryview_parameter = function()
	local xs = ffi.new("double[3]", {1, 2, 3})
	local ys = ffi.new("double[3]", {4, 5, 6})
	local decl = fhk.new(
		fhk.group("a",
			fhk.named("x", fhk.array(xs, fhk.c.space1(3))),
			fhk.named("y", fhk.array(ys, fhk.c.space1(3))),
			fhk.shape(3)
		),
		fhk.group("b", fhk.shape(1))
	)
	decl:graph(
		fhk.g.model(
			"b#m",
			"a#x" *fhk.g.choose "space",
			"a#y" *fhk.g.choose "space",
			"->",
			"z" *fhk.g.as "double",
			fhk.g.impl.Python("models", "dot_seq")
		)
	)
	local solver = decl { "b#z", value=fhk.scalar() }
	decl:ready()
	local result = solver()
	assert(result.b_z == 1*4+2*5+3*6)
end

test_call_py_return_list = function()
	local xs = ffi.new("double[3]", {1, 2, 3})
	local decl = fhk.new(
		fhk.group("a",
			fhk.named("x", fhk.array(xs, fhk.c.space1(3))),
			fhk.shape(3)
		),
		fhk.group("b", fhk.shape(1))
	)
	decl:graph(
		fhk.g.model(
			"b#m",
			"a#x" *fhk.g.choose "space",
			"->",
			"a#y" *fhk.g.choose "space" *fhk.g.as "double",
			fhk.g.impl.Python("models", "sq_list")
		)
	)
	local solver = decl { "a#y" }
	decl:ready()
	local result = solver()
	assert(result.a_y[0] == 1 and result.a_y[1] == 4 and result.a_y[2] == 9)
end

test_call_py_multireturn_tuple = function()
	local xs = ffi.new("double[3]", {1, 2, 3})
	local decl = fhk.new(
		fhk.group("a",
			fhk.named("x", fhk.array(xs, fhk.c.space1(3))),
			fhk.shape(3)
		),
		fhk.group("b", fhk.shape(1))
	)
	decl:graph(
		fhk.g.model(
			"b#m",
			"a#x" *fhk.g.choose "space",
			"->",
			"z" *fhk.g.as "double",
			"a#y" *fhk.g.choose "space" *fhk.g.as "double",
			fhk.g.impl.Python("models", "multiret")
		)
	)
	local solver = decl { "a#y", "b#z" }
	decl:ready()
	local result = solver()
	assert(result.b_z[0] == 1+2+3 and result.a_y[0] == 1 and result.a_y[1] == 2 and result.a_y[2] == 3)
end

test_call_py_error = function()
	local decl = fhk.new(fhk.group("a", fhk.shape(1)))
	decl:graph(
		fhk.g.model(
			"a#m", "->", "x" *fhk.g.as "double",
			fhk.g.impl.Python("models", "errfunc")
		)
	)
	local solver = decl { "a#x" }
	decl:ready()
	assert(fails(solver, "something happened"))
end

test_call_py_invalid_signature = function()
	local decl = fhk.new(fhk.group("a", fhk.shape(1)))
	decl:graph(
		fhk.g.model(
			"a#m", "->", "x" *fhk.g.as "double",
			fhk.g.impl.Python("models", "ident_unannotated")
		)
	)
	local solver = decl { "a#x" }
	decl:ready()
	assert(fails(solver, "missing 1 required positional argument"))
end

test_call_py_return_rank_mismatch = function()
	local xs = ffi.new("double[3]", {1, 2, 3})
	local decl = fhk.new(
		fhk.group("a",
			fhk.named("x", fhk.array(xs, fhk.c.space1(3))),
			fhk.shape(3)
		),
		fhk.group("b", fhk.shape(1))
	)
	decl:graph(
		fhk.g.model(
			"b#m",
			"a#x" *fhk.g.choose "space" *fhk.g.as "double",
			"->",
			"y" *fhk.g.as "double",
			fhk.g.impl.Python("models", "rank_mismatch")
		)
	)
	local solver = decl { "b#y" }
	decl:ready()
	assert(fails(solver, "object is not subscriptable"))
end
