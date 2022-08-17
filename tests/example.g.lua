model () {
	params [[
		x
		b#y ~m
	]],
	returns [[
		z
		w
	]] *as "double",
	impl.Lua("example_mod", "a_mod")
}
