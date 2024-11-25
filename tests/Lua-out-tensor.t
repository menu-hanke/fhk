# vim: ft=fhk

model global a = call Lua["return function(xs) xs[0]=1 xs[1]=2 xs[2]=3 end"] (out[3])

### result { a={1,2,3} }
