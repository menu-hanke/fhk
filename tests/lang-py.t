-- vim: ft=lua:
local fhk = require "fhk"
local ffi = require "ffi"

function test_py_call_unannotated()
	local graph = fhk.graph(function()
		var "x" {
			ctype "double",
			function() return 1 end
		}
		model () {
			params "x",
			returns "y" *as "double",
			impl.Python("models", "ident_unannotated")
		}
	end)
	local query = graph:query "y"
	graph:prepare()
	assert(query().y == 1)
end

function test_py_call_annotated_scalar()
	local graph = fhk.graph(function()
		var "x" {
			ctype "double",
			function() return 1 end
		}
		model () {
			params "x",
			returns "y" *as "int",
			impl.Python("models", "ident_conv_annotated")
		}
	end)
	local query = graph:query "y"
	graph:prepare()
	assert(query().y == 1)
end

function test_py_call_memoryview_parameter()
	local xs = ffi.new("double[3]", {1, 2, 3})
	local ys = ffi.new("double[3]", {4, 5, 6})
	local graph = fhk.graph(function()
		var "g" { function() return fhk.space1(3) end }
		var "g#x" { fhk.array(xs, fhk.space1(3)) }
		var "g#y" { fhk.array(ys, fhk.space1(3)) }
		model () {
			params [[
				g#x ~*
				g#y ~*
			]],
			returns "z" *as "double",
			impl.Python("models", "dot_seq")
		}
	end)
	local query = graph:query "z"
	graph:prepare()
	assert(query().z == 1*4+2*5+3*6)
end

function test_py_call_return_list()
	local xs = ffi.new("double[3]", {1, 2, 3})
	local graph = fhk.graph(function()
		var "g" { function() return fhk.space1(3) end }
		var "g#x" { fhk.array(xs, fhk.space1(3)) }
		model "global#mod" {
			params "g#x ~*",
			returns "g#y ~*" *as "double",
			impl.Python("models", "sq_list")
		}
	end)
	local query = graph:query "g#y"
	graph:prepare()
	local result = query()
	assert(result.g_y[0] == 1 and result.g_y[1] == 4 and result.g_y[2] == 9)
end

function test_py_call_py_multireturn_tuple()
	local xs = ffi.new("double[3]", {1, 2, 3})
	local graph = fhk.graph(function()
		var "g" { function() return fhk.space1(3) end }
		var "g#x" { fhk.array(xs, fhk.space1(3)) }
		model "global#mod" {
			params "g#x ~*",
			returns [[
				z
				g#y ~*
			]] *as "double",
			impl.Python("models", "multiret")
		}
	end)
	local query = graph:query("z", "g#y")
	graph:prepare()
	local result = query()
	assert(result.z == 1+2+3)
	assert(result.g_y[0] == 1 and result.g_y[1] == 2 and result.g_y[2] == 3)
end

function test_py_call_optional()
	local xs = ffi.new("int[2]", {-1, 2})
	local graph = fhk.graph(function()
		var "g" { function() return fhk.space1(2) end }
		var "g#x" { fhk.array(xs, fhk.space1(2)) }
		model "g#mod" {
			params "x",
			returns "y" *as "int",
			impl.Python("models", "optional")
		}
	end)
	local query = graph:query "g#y"
	graph:prepare()
	local result = query()
	assert(result.g_y[0] == 123 and result.g_y[1] == 2)
end

function test_py_call_error()
	local graph = fhk.graph(function()
		model () {
			returns "x" *as "double",
			impl.Python("models", "errfunc")
		}
	end)
	local query = graph:query "x"
	graph:prepare()
	assert(fails(query, "something happened"))
end

function test_py_call_invalid_signature()
	local graph = fhk.graph(function()
		model () {
			returns "x" *as "double",
			impl.Python("models", "ident_unannotated")
		}
	end)
	local query = graph:query "x"
	graph:prepare()
	assert(fails(query, "missing 1 required positional argument"))
end

function test_py_call_return_rank_mismatch()
	local xs = ffi.new("double[3]", {1, 2, 3})
	local graph = fhk.graph(function()
		var "g" { function() return fhk.space1(3) end }
		var "g#x" { fhk.array(xs, fhk.space1(3)) }
		model () {
			params "g#x ~*",
			returns "y" *as "double",
			impl.Python("models", "rank_mismatch")
		}
	end)
	local query = graph:query "y"
	graph:prepare()
	assert(fails(query, "object is not subscriptable"))
end
