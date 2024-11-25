# vim: ft=fhk

table t[3]
model t[i] idx = i+1
model global s = call Lua["return function(xs) local s = 0 for i=0, #xs-1 do s=s+xs[i] end return s end"] (t.idx)

### result { s=1+2+3 }
