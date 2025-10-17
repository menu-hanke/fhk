# vim: ft=fhk

table t[10]
model t[i] x = i*query.c
model global x = sum(t.x)

### result({x=450},{c=10})
