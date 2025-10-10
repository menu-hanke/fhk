# vim: ft=fhk

table t[3]
model t[i] x = i+1

macro var t _'$expr = $expr
macro var global T'{$expr where $filter} = sum(t._'{$expr}[which(t._'{$filter})])
macro var global T'{$expr where} = sum(t._'{$expr})

macro var global X'$filter = T'{x where $filter}

model global XX = X'{}
model global X23 = X'{x >= 2}

### result { X=1+2+3, XX=1+2+3, X23=2+3 }
