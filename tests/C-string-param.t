# vim: ft=fhk

# TODO: should be `const char *`, but lang_C can't parse that (yet).
# TODO: fix (and by fix i mean implement) C output type conversion
model global x: i32 = call C ["atoi"] ("123": char *): int

### result { x=123 }
