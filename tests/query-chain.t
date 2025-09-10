# vim: ft=fhk

model global x = call Lua ["return function(x) return x end"] (query.x)

### local query0 = G:query("x")
### local query1 = G:query("x+1")
### compile()
### local inst = newinstance()
### check({image[query0](inst, {x=1}):unpack()}, {1})
### check({image[query0](inst, {x=2}):unpack()}, {2})
