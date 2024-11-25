# vim: ft=fhk

table t[5]
model t[i] idx = i
model global idx2 = which(t.idx>2)
model global s = sum(t.idx[idx2])

### result { s=3+4 }
