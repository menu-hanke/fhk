local driver = require "fhk_driver"
local ffi = require "ffi"

-- modcall lua expression (template)
--     expr         template
local function modcallexpr(J, o, e)
	local code = driver.code()
	code.upv.cast = ffi.cast
	local p = {}
	e = e:gsub("%$(%d+)", function(i)
		i = tonumber(i)
		if not p[i] then
			local ctp = code:upval(ffi.typeof("$*", o.params[i].var.ctype))
			code.src:putf("local p%d = cast(%s, S.edges[%d].p)[0]\n", i, ctp, i-1)
			p[i] = true
		end
		return string.format("p%d", i)
	end)
	local comma = ""
	for i, r in ipairs(o.returns) do
		local ctp = code:upval(ffi.typeof("$*", r.var.ctype))
		code.src:put(comma)
		code.src:putf("cast(%s, S.edges[%d].p)[0]", ctp, #o.params+i-1)
		comma = ","
	end
	code.src:put(" = ", e, "\n")
	code.name = string.format("=fhk:modcallexpr<%s>", e)
	return code:emitjmp(J)
end

local function modcallconst(J, o, v)
	local mode = driver.getmode(o)
	local code = driver.code()
	code.upv.cast = ffi.cast
	for i,r in ipairs(o.returns) do
		local uv = code:upval(#v == 1 and v[1] or v[i])
		local ctp = code:upval(ffi.typeof("$*", r.var.ctype))
		if mode:sub(#o.params+i, #o.params+i) == "s" then
			code.src:putf("cast(%s, S.edges[%d].p)[0] = %s\n", ctp, #o.params+i-1, uv)
		else
			code.upv.tonumber = tonumber
			code.src:putf([[
				do
					local vp = cast(%s, S.edges[%d].p)
					for i=0, tonumber(S.edges[%d].n)-1 do
						vp[i] = %s
					end
				end
			]], ctp, #o.params+i-1, #o.params+i-1, uv)
		end
	end
	code.name = string.format("=fhk:modcallconst<%s>", v)
	return code:emitjmp(J)
end

local function expr_load(J, o)
	if type(o.impl[1]) == "string" then
		return modcallexpr(J, o, o.impl[1])
	else
		return modcallconst(J, o, o.impl)
	end
end

return {
	load = expr_load
}
