fhk
===
**fhk** *(funktiohakukone, function search engine)* is a high-performance cross-language
computational graph solver.
Given a list of "models", each having a list of input and output "variables",
fhk computes values for some set of output variables given values for some set of input variables.
Models can be implemented in multiple languages, and fhk can cross-call between languages.

## Example
The following example uses the Lua api to find the value of $x_5$, given $x_1$, $x_2$
and models that map $(x_1, x_2) \mapsto x_3$ and $(x_3, x_4) \mapsto x_5$.
```lua
local fhk = require "fhk"

-- this will hold the value of x4.
local x4

-- create a new graph.
-- fhk can read graphs from files or you can define with an inline function.
local graph = fhk.graph(function()
	-- x1, x2 are given double precision variables, both with constant value 2.
	var "x1" { function() return 2 end }
	var "x2" { function() return 2 end }
	-- x4 is a given double precision variable that reads its value from the "x4" variable.
	var "x4" { function() return x4 end }
	-- this model computes x4 = x1 + x2
	model () {
		params "x1 x2",
		returns "x3",
		function(x1, x2) return x1+x2 end
	}
	-- this model computes x5 = x3 - x4
	model () {
		params "x3 x4",
		returns "x5",
		function(x3, x4) return x3-x4 end
	}
end)

-- `graph:query(...)` returns a function that solves the queried variables from the graph.
local quick_maths = graph:query "x5"

-- graph:prepare() builds the search data structures, and must be called after the graph
-- and queries have been defined.
graph:prepare()

-- we can now query the graph.
-- let's set x4 first.
x4 = 1
-- fhk will compute:
--   x3 = x1 + x2 = 2 + 2 = 4
--   x5 = x3 - x4 = 4 - 1 = 3
local result = quick_maths()

-- this outputs: 3
print(result.x5)
```

## Building

For both the Lua and Python extensions you need:
* gcc. clang is not supported because it doesn't have global register variables.
* A LuaJIT binary to compile bytecode with.

### Lua extension
Run `make lua` to obtain `fhk.so` or `fhk.dll` depending on your platform.
You can use the library from Lua with `local fhk = require "fhk"`.

### Python extension
You need:
* LuaJIT/Lua 5.1 headers (`LUAJIT_I`)
* LuaJIT static or shared library (`LUAJIT_L`)
* Python (`PYTHON`)
* Cython (`CYTHON`)

Run `make pyx` to obtain a CPython extension module.
You can use the library from Python with `import fhk`.

### Windows concerns
If you're building the Lua extension, you need to link it against `lua51.dll`.
If you're building the Python extension in MinGW to be used outside MinGW, make sure `PYTHON`
points to a non-MinGW Python binary.

## Similar projects
fhk resembles [GraphTik](https://github.com/pygraphkit/graphtik)/[GraphKit](https://github.com/yahoo/graphkit)
and [schedula](https://github.com/vinci1it2000/schedula).
In fact, fhk and schedula were both created for almost the same purpose: running simulations.
Some differences between the solvers are:
- GraphKit and schedula are Python-only, while fhk has host APIs for Lua and Python,
  and the solver itself is language-agnostic (model implementation languages are pluggable).
- schedula can run in parallel, while fhk is single-threaded (per solver).
- schedula's solver flows data starting from inputs, and uses a weighted Dijkstra-style
  algorithm to select models. fhk's solver backtracks from output variables and selects a
  subgraph that minimizes a cost function.
