# vim: ft=fhk

model global a,b = call Lua["return function() return 1,2 end"] ()

### result { a=1, b=2 }
