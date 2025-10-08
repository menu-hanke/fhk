# vim: ft=fhk

model global x = select(true, [1,2,3], [4,5,6])

### result { x={1,2,3} }
