# vim: ft=fhk

table t[10]
model t[i] x = i
model global idx = which(t.x > 5)

### result { idx={6,7,8,9} }
