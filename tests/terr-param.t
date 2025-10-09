# vim: ft=fhk

func f(x) = x
model global x = f(1,2)

### compilefail("x", "type checking error")
