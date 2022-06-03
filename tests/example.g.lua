model "a#mod" {
	params { "x", "b#y" *choose "a->b" },
	returns { "z", "w" } *as "double",
	impl.LuaJIT("example_mod", "a_mod")
}
