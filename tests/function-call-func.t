# vim: ft=fhk

func g(x) = f(x)*2
func f(x) = x+1
model global x = g(10)

### result {x=(10+1)*2}
