# vim: ft=fhk

model global x = select([true, false, true], 1, 2)

### result { x={1,2,1} }
