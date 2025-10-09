# vim: ft=fhk

model global x = call Lua ["return tonumber"] ("123")

### result { x=123 }
