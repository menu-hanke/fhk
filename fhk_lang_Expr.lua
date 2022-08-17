local driver = require "fhk_driver"

-- TODO: combine lang_Const with this.

-- modcall lua expression (template)
--     expr         template
local function modcallexpr(g, expr)
	g.code.upv.cast = ffi.cast
	local comma = ""
	local p = {}
	expr = expr:gsub("%$(%d+)", function(i)
		if not p[i] then
			local ctp = driver.upval(g.code, ffi.typeof("$*", r.params[i].ctype))
			g.src:putf("local p%d = cast(%s, S.edges[%d].p)[0]\n", ctp)
			p[i] = true
		end
		return string.format("p%d", i)
	end)
	for i, r in ipairs(g.obj.returns) do
		local ctp = driver.upval(g.code, ffi.typeof("$*", r.var.ctype))
		g.src:putf("cast(%s, S.edges[%d].p)[0]", ctp, #g.obj.params+i)
		g.src:put(comma)
		comma = ","
	end
	g.src:put(" = ", expr, "\n")
	g.upv.name = string.format("=fhk:modcallexpr<%s>", op.expr)
end

return {
	load = modcallexpr
}
