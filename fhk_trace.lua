local ffi = require "ffi"
local cdef = require "fhk_cdef"
local buffer = require "string.buffer"

local colorterm = os.getenv("COLORTERM") ~= nil

local colors = {
	var      = 36,
	model    = 33,
	zerocost = 32,
	infcost  = 31,
	skip     = 31,
	inst     = 1,
	idx      = 34,
	ctype    = 35,
	reset    = 0
}

local function coloron(color)
	if type(color) == "string" then color = colors[color] end
	return "\027["..(color or 0).."m"
end
local function coloroff() return "" end

local function costcolor(cost)
	if cost == math.huge then return "infcost" end
	if cost == 0 then return "zerocost" end
	return ""
end

---- graph dump ----------------------------------------

local tagchar = "VMXDCPR"
local tagmask = "mgpdsjrx"

local function putcf(buf, color, fmt, ...)
	if color then buf:put(color) end
	buf:putf(fmt, ...)
	if color then buf:put("\027[m") end
end

local function dumpcost(buf, cost, color)
	if color then buf:put(color(costcolor(cost))) end
	local num = #buf
	buf:put(cost)
	num = #buf - num
	if color then buf:put("\027[m") end
	return num
end

local function dumpobj(graph, buf, handle, cobj, color)
	local obj = graph.objs[handle]
	buf:putf("0x%04x ", handle)
	if obj and obj.idx then
		putcf(buf, color "idx", "%04d", obj.idx)
	else
		buf:put("    ")
	end
	local tag = cobj.tag
	buf:put(" ", color(bit.band(tag, cdef.mtagmask.s) ~= 0 and "skip" or cobj.what))
	local typ = bit.band(tag, cdef.mtagmask.T)
	buf:putf(tagchar:sub(typ+1,typ+1))
	for i=1, #tagmask do
		local c = tagmask:sub(i,i)
		buf:put(bit.band(tag, cdef.mtagmask[c]) == 0 and "-" or c)
	end
	buf:put(color "reset")
	buf:putf(" %-15s ", obj and obj.name or "")
	if bit.band(tag, cdef.mtagmask.s) ~= 0 then
		if bit.band(tag, cdef.mtagmask.p) == 0 and not (obj.computed or obj.impl) then
			buf:put(color "infcost", (" "):rep(25), "missing", color "reset")
		end
		return
	end
	buf:put(" ")
	if cobj.what == "var" or cobj.what == "model" then
		buf:put("[")
		local num = dumpcost(buf, cobj.clo, color)
		buf:put(", ")
		num = num + dumpcost(buf, cobj.chi, color)
		buf:put("]")
		if num < 8 then buf:put((" "):rep(8-num)) end
	end
	if obj and type(obj.ctype) == "cdata" then
		putcf(buf, color "ctype", "%-9s", tostring(obj.ctype):match("ctype<([^>]+)>"))
	else
		buf:put((" "):rep(10))
	end
	if obj and obj.jump then
		buf:put("->")
		putcf(buf, color "idx", "%04d", obj.jump)
		if obj.impl then
			buf:put(" ", tostring(obj.impl.loader))
		end
	end
end

local function dumpgraph(graph, color)
	color = (color == false or not colorterm) and coloroff or coloron
	local buf = buffer.new()
	for h,o in graph.M:opairs() do
		if o.what == "var" or o.what == "model" then
			dumpobj(graph, buf, h, o, color)
			buf:put("\n")
		end
	end
	return buf:get()
end

---- subset dump ----------------------------------------

local function intervalstr(first, znum)
	if znum == 0 then return tostring(first) end
	return first.."..+"..znum
end

local function dumpsubset(ss)
	if ss == -1 then return "(empty)" end
	if ss == -2 then return "(undef)" end
	if ss < -1 then
		local buf = buffer.new()
		buf:put("{")
		local pk = ffi.cast("fhk_pkref", bit.bnot(ss))
		while true do
			local first = pk[0] + bit.lshift(pk[1], 8) + bit.lshift(bit.band(pk[2], 0xf), 16)
			local znum = bit.rshift(pk[2], 4) + bit.lshift(pk[3], 4) + bit.lshift(pk[4], 12)
			buf:put(" ", intervalstr(first, znum))
			if pk[5] == 0 and pk[6] == 0 and pk[7] == 0 then break end
			pk = pk+5
		end
		buf:put(" }")
		return buf:get()
	end
	return intervalstr(bit.tobit(ss), tonumber(bit.rshift(ss, 32)))
end

local ssctp = ffi.typeof("$*", ffi.metatype(
	"struct { fhk_subset ss; }",
	{ __tostring = function(self) return dumpsubset(self.ss) end }
))

---- jump table trace ----------------------------------------

local function tracejump(name, what, idx, inst, color)
	io.stderr:write(
		color "idx",
		string.format("%04d", idx),
		color "reset",
		color "inst",
		string.format(":%04d", inst),
		color "reset",
		color(what),
		string.format(" %-15s", name),
		color "reset",
		" :: "
	)
end

local function tracevalue(v, n)
	if n > 1 then io.stderr:write("[ ") end
	local space = ""
	for i=1, n do
		io.stderr:write(space, tostring(v[i-1]))
		space = " "
	end
	if n > 1 then io.stderr:write(" ]") end
end

local function tracevar(S, name, ctypeptr, color)
	tracejump(name, "var", S.idx, S.inst, color)
	-- assume it's set, otherwise the solver will fail on the next continue anyway.
	local v = S:V(S.idx)
	if v ~= nil then
		tracevalue(ffi.cast(ctypeptr, v)+S.inst, 1)
	end
	io.stderr:write("\n")
end

local function tracemodel(S, call, color)
	tracejump(call.name, "model", S.idx, S.inst, color)
	local space = ""
	for i=1, #call do
		if i == call.np+1 then
			io.stderr:write(color(1), " => ", color "reset")
			space = ""
		end
		io.stderr:write(
			space,
			color "var",
			call[i].name,
			color "reset",
			"="
		)
		tracevalue(ffi.cast(call[i].ctypeptr, S.edges[i-1].p), tonumber(S.edges[i-1].n))
		space = " "
	end
	io.stderr:write("\n")
end

local function ctypeptr(graph, var)
	if bit.band(graph.M:get(var.handle).tag, cdef.mtagmask.m) ~= 0 then
		return ssctp
	end
	return ffi.typeof("$*", var.ctype)
end

local function putedges(graph, mod, call, edges)
	for _,e in ipairs(edges) do
		local name = e.var.name
		if name and mod.name and e.var.group == mod.group then
			local n = name:match("#(.*)$")
			if n then name = n end
		end
		table.insert(call, {
			name = name or tostring(e.var.idx),
			ctypeptr = ctypeptr(graph, e.var)
		})
	end
end

local function tracehook(graph, obj, what)
	local color = colorterm and coloron or coloroff
	local name = obj.name or tostring(obj.idx)
	local post
	if what == "var" then
		post = function(S) return tracevar(S, name, ctypeptr(graph, obj), color) end
	elseif what == "model" then
		local call = { name=name, np=#obj.params }
		putedges(graph, obj, call, obj.params)
		putedges(graph, obj, call, obj.returns)
		post = function(S) return tracemodel(S, call, color) end
	end
	return function() return post end
end

--------------------------------------------------------------------------------

return {
	dumpgraph = dumpgraph,
	tracehook = tracehook
}
