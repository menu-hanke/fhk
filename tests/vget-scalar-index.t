# vim: ft=fhk

table t[3]
model t[i] x = 100*i
model global x2 = t.x[2]

### result { x2 = 200 }
