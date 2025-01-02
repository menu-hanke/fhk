# vim: ft=fhk

table t[:,[1,2,3]]
model t[i,j] x = 100*i + j
model global x = t.x[::]

### result { x={0, 100, 101, 200, 201, 202} }
