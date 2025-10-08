# vim: ft=fhk

model global a = [2,3,4]
model global x = select(true, 1, a)
model global y = select(false, 1, a)

### result { x={1,1,1}, y={2,3,4} }
