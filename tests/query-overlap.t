# vim: ft=fhk

model global x = query.a + query.b
model global y = query.a * query.c

### local queryX = G:query("x")
### local queryY = G:query("y")
### compile()
### local inst = newinstance()
### check({image[queryX](inst, {a=2, b=3}):unpack()}, {2+3})
### check({image[queryY](inst, {a=3, c=4}):unpack()}, {3*4})
