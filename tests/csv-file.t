# vim: ft=fhk

model global x = call Table ["timber.csv"] (
	1,
	150: atleast,
	415: interpolate,
	out
)

### result { x=58 }
