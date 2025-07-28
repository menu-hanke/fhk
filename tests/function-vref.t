# vim: ft=fhk

func subx(a) = a-x
model global x = 1
model global y = subx(10)

### result {y=9}
