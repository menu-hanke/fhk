# vim: ft=fhk

model global x = 123
model global x = "123"

### compilefail("x", "type checking error: cannot assign")
