# vim: ft=fhk

model global x = select(true, "a", "b") = "a"

### result { x=true }
