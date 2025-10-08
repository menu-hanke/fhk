# vim: ft=fhk

model global a = select(true, 1, 2)
model global b = select(a=2, 3, 4)

### result { a=1, b=4 }
