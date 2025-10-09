# vim: ft=fhk

model global a = "abc"="abc"
model global b = "abc"="ab"

### result { a=true, b=false }
