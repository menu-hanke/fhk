# vim: ft=fhk

model global a = min(1, 2, 3)
model global b = max(0, [-1, 0, 1])

### result { a=1, b={0,0,1} }
