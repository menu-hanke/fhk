## fhk

**fhk** _(**f**unktio**h**aku**k**one, function search engine)_ is an embeddable dataflow engine library: you give fhk rules (*models*) for computing values of *variables*, and fhk computes the values you query. Models are described in fhk's DSL. Model functions can be implemented in multiple programming languages, see [here](#building) for a list of supported languages.

## Example

This is a model definition file in fhk's DSL:
```
model global {
    four = 2 + 2       # two plus two is four
    three = four - 1   # minus one, that's three
}
```

This is how you use the models via fhk's Lua API:
```lua
local fhk = require "fhk"

-- 1. create a new graph.
-- A graph holds model, variable, and query definitions.
local G = fhk.newgraph()

-- 2. load the model definitions.
G:define(io.open("quick-maths.fhk"):read("*a"))

-- 3. define our query. the first argument is a *table* name, followed by any
-- number of expressions.
local query = G:newquery("global", "three")

-- 4. compile the graph.
-- this must be done after all models and queries are defined, and before any
-- query can be executed.
G:compile()

-- 5. create an instance.
-- a compiled graph is immutable, while an instance is stateful and holds
-- values of previously computed variables so that fhk doesn't need to compute
-- them again. typically you want to create multiple instances from a compiled
-- graph.
local inst = G:newinstance()

-- 6. execute the query.
-- by default the query returns a struct with the values of all the
-- expressions. the unpack() methods returns each value.
assert(inst:exec(query):unpack() == 3)
```
## Building

You can build fhk with:

```
cargo build --release
```

This builds a Lua library by default, which is currently the only supported host language.
You can enable the following features:

|feature |default|description|
|--------|-------|-----------|
|host-Lua|:white_check_mark:|Build a Lua library.|
|lang-C  |:white_check_mark:|Enable `call C` support.|
|lang-R  |:white_check_mark:|Enable `call R` support.|
|lang-Lua|:white_check_mark:|Enable `call Lua` support.|

fhk currently supports only x64 Linux/Windows.

## DSL reference

(TODO)
