# vim: ft=fhk

macro var global lua'$code = call Lua["return function() $code end"] ()
model global a = lua'{local a = 1 local b = 2 return a+b}

### result { a=3 }
