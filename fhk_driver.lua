local ctypes = require "fhk_ctypes"
local C = require "fhk_clib"
local buffer = require "string.buffer"
local ffi = require "ffi"
require "table.clear"
require "table.new"

local function graph()
	local M, err = ctypes.mut()
	if not M then error(tostring(err)) end
	ctypes.gc(M)
	return {
		M      = M,
		J      = {},
		buf    = buffer.new(),

		-- [] => {
		--     handle
		--     tag = "group"
		--     name
		--     idx               L
		--     slot              L
		--     jfunc?             J
		-- }
		groups = {},

		-- [] => {
		--     handle
		--     tag = "map"
		--     name
		--     flags
		--     rank?
		--     idx               L
		--     slot              L
		--     jfunc?             J
		-- }
		maps   = {},

		-- [] => {
		--     handle
		--     tag = "var"
		--     name
		--     ctype                          before layout: possible ctidset,  after layout: ctype
		--     idx               L
		--     slot?             L
		--     jfunc?             J
		-- }
		vars   = {},

		-- [] => {
		--     handle
		--     tag = "model"
		--     name
		--     idx               L
		--     slot              L
		--     jfunc?             J
		--     params, returns [] => {
		--         handle
		--         rank?
		--         tag = "edge"
		--         var -> vars
		--     }
		-- }
		models = {},

		-- [] => {
		--     handle
		--     tag = "guard"
		--     name
		--     idx               L
		-- }
		guards = {}
	}
end

local ident = {
	tag = "builtin",
	flags = "is",
	handle = ctypes.handles.ident
}

local space = {
	tag = "builtin",
	flags = "kv",
	handle = ctypes.handles.space
}

-- alias for space that defaults to scalar.
local only = {
	tag = "builtin",
	flags = "ks",
	handle = ctypes.handles.space
}

local function handlestr(graph, handle)
	if handle == ident.handle then return "(ident)" end
	if handle == space.handle then return "(space)" end
	for _,tab in pairs(graph) do
		if type(tab) == "table" then
			for _,x in ipairs(tab) do
				if x.handle == handle then
					return x.name
				end
			end
		end
	end
end

local function patcherror(graph, err)
	if err.handle then
		err.handle = handlestr(graph, err.handle) or err.handle
	end
	return err
end

local function checke(graph, e)
	if e then
		error(tostring(patcherror(graph, e)))
	end
end

local function checkv(graph, x, e)
	if x then
		return x
	else
		error(tostring(patcherror(graph, e)))
	end
end

local function checknil(x, fmt, ...)
	if x ~= nil then return x end
	error(string.format(fmt, ...))
end

---- building ----------------------------------------

local function namehandle(tag, handle)
	return string.format("%s@0x%x", tag, handle)
end

local setdsym = (function()
	if ctypes.dsym then
		return function(graph, handle, name)
			graph.M:set_dsym(handle, name)
		end
	else
		return function() end
	end
end)()

local function addgroup(graph, name)
	local handle = checkv(graph, graph.M:add_group())
	local name = name or namehandle("group", handle)
	setdsym(graph, handle, name)
	local group = {
		handle = handle,
		tag    = "group",
		name   = name
	}
	table.insert(graph.groups, group)
	return group
end

local function addmap(graph, flags, name)
	local handle
	if not flags:match("[sv]") then
		-- this is a safe default.
		-- at worst it's a runtime error in whatever scripting language the edge points at.
		flags = flags .. "v"
	end
	if flags:match("i") then
		handle = checkv(graph, graph.M:add_mapi())
	elseif flags:match("k") then
		handle = checkv(graph, graph.M:add_mapk())
	else
		error(string.format("invalid map flag: '%s'", flags))
	end
	local name = name or namehandle("map", handle)
	setdsym(graph, handle, name)
	local map = {
		handle = handle,
		tag    = "map",
		name   = name,
		flags  = flags,
	}
	table.insert(graph.maps, map)
	return map
end

local function umap2(forward, inverse)
	return {
		tag    = "umap2",
		flags  = forward.flags, -- this is saved for rank checks in modcall compilation
		handle = ctypes.handle2(forward.handle, inverse.handle)
	}
end

local function addmodel(graph, group, k, c, name)
	local handle = checkv(graph, graph.M:add_model(group.handle, k, c))
	local name = name or namehandle("model", handle)
	setdsym(graph, handle, name)
	local model = {
		handle  = handle,
		tag     = "model",
		name    = name,
		params  = {},
		returns = {}
	}
	table.insert(graph.models, model)
	return model
end

local function setcost(graph, model, k, c)
	if model.idx then
		-- we don't do layout invalidations here even if the C api would allow it.
		-- this would also invalidate the jump table.
		error("setcost called on a layouted graph")
	end
	graph.M:set_cost(model.handle, k, c)
end

local function cttoid(x)
	if type(x) == "cdata" or type(x) == "string" then
		return tonumber(ffi.typeof(x))
	end
	if type(x) == "table" then
		return x.typeid
	end
	if type(x) == "number" then
		return x
	end
end

local function ctids(x)
	if type(x) == "table" then
		if x.typeid then
			return ctids(x.typeid)
		else
			local out = {}
			for i,ct in ipairs(x) do
				out[i] = cttoid(ct)
			end
			table.sort(out)
			return out
		end
	end
	return x and {cttoid(x)}
end

local function ctintersect(A, B)
	if not (A and B) then return A or B end
	local C = {}
	local i, j = 1, 1
	while i <= #A and j <= #B do
		local a, b = A[i], B[j]
		if a < b then
			i = i+1
		elseif b < a then
			j = j+1
		else
			table.insert(C, a)
			i = i+1
			j = j+1
		end
	end
	return C
end

local function setctype(var, cts)
	var.ctype = ctintersect(var.ctype, ctids(cts))
end

local function addvar(graph, group, name, cts)
	local handle = checkv(graph, graph.M:add_var(group.handle))
	local name = name or namehandle("var", handle)
	setdsym(graph, handle, name)
	local var = {
		handle = handle,
		tag    = "var",
		name   = name,
		ctype  = ctids(cts),
	}
	table.insert(graph.vars, var)
	return var
end

local function setop(graph, guard, op, arg)
	if type(op) == "string" then
		if type(guard.var.ctype) ~= "cdata" then
			-- not layouted yet, defer
			guard.op, guard.arg = op, arg
			return
		end
		op, arg = ctypes.guard(op, arg, guard.var.ctype)
	end
	checke(graph, graph.M:set_opcode(guard.handle, op, arg))
end

local function addguard(graph, var, name, op, arg)
	local handle = checkv(graph, graph.M:add_guard(var.handle))
	local name = name or namehandle("guard", handle)
	setdsym(graph, handle, name)
	local guard = {
		handle = handle,
		tag    = "guard",
		var    = var,
		name   = name
	}
	table.insert(graph.guards, guard)
	if op then
		setop(graph, guard, op, arg)
	end
	return guard
end

local function addparam(graph, model, var, map2)
	local edge = {
		handle = checkv(graph, graph.M:add_param(model.handle, var.handle, map2.handle)),
		tag    = "edge",
		-- for modcalls
		var    = var,
		map2   = map2
	}
	table.insert(model.params, edge)
	return edge
end

local function addreturn(graph, model, var, map2)
	local edge = {
		handle = checkv(graph, graph.M:add_return(model.handle, var.handle, map2.handle)),
		tag    = "edge",
		-- for modcalls
		var    = var,
		map2   = map2
	}
	table.insert(model.returns, edge)
	return edge
end

local function addcheck(graph, model, guard, map2, penalty)
	return {
		handle = checkv(graph, graph.M:add_check(model.handle, guard.handle, map2.handle, penalty)),
		tag    = "check",
		guard  = guard
	}
end

local function setrank(x, rank)
	x.rank = rank
end

local function pin(graph, x)
	graph.M:pin(x.handle)
end

---- pruning ----------------------------------------

local function prune(graph)
	checke(graph, graph.M:prune())
end

---- layouting ----------------------------------------
--
-- Q: why not use `tonumber(hex, 16)`?
-- A: someone at microsoft thought it would be funny to make `long` 4 bytes.
--    luajit uses `strtoul` to parse the number (for bases other than 10)
--    so now we have a situation where `tonumber` won't work on windows for
--    numbers that don't fit in 4 bytes, *unless the base is 10*.
--    base-10 is special-cased with a custom function that handles them just fine.
local function cdataptr(cdata)
	local hex = string.format("%p", cdata):sub(3)
	local lo = tonumber(hex:sub(-8), 16)
	local hi = tonumber(hex:sub(1, -9), 16) or 0
	return ffi.cast("intptr_t", lo) + ffi.cast("intptr_t", hi)*(2^32)
end

-- XXX: this is a hack that depends on LuaJIT internals.
-- basically we create a dummy cdata and modify the internal ctypeid
-- to create a counterfeit ctype reference.
-- obviously don't call this with an invalid ctype id, terrible things will happen.
local function ctfromid(id)
	-- it doesn't matter what type this holds, we will overwrite it
	local dummy = ffi.typeof("void")

	-- very illegal stuff happens here
	local cdataptr = ffi.cast("uint32_t *", cdataptr(dummy))
	cdataptr[0] = id

	-- dummy now refers to our ctype!
	return dummy
end
jit.off(ctfromid) -- obviously

local function ctsstr(cts)
	if not cts then return "<any>" end
	local out = {}
	for i,t in ipairs(cts) do
		out[i] = tostring(ctfromid(t))
	end
	return string.format("{%s}", table.concat(out, ", "))
end

local function toctype(x)
	if type(x) == "table" then
		if #x ~= 1 then
			return
		end
		-- this should be a cts set
		assert(type(x[1] == "number"))
		return ctfromid(x[1])
	end
	if x then
		-- it's already resolved
		assert(type(x) == "cdata")
		return x
	end
end

local function guardcheck(graph)
	for _,g in ipairs(graph.guards) do
		if g.op then
			local v = g.var
			v.ctype = toctype(v.ctype)
				or error(string.format("non-unique ctype: %s (deferred guard: %s)", v.name, g.name))
			local op, arg = ctypes.guard(g.op, g.arg, v.ctype)
			if not op then
				error(string.format("guard opcode `%s' is not applicable for ctype `%s'", g.op, v.ctype))
			end
			checke(graph, graph.M:set_opcode(g.handle, op, arg))
		end
	end
end

local function typecheck(graph)
	local fails
	for _,v in ipairs(graph.vars) do
		v.ctype = toctype(v.ctype)
		if v.ctype then
			checke(graph, graph.M:set_size(v.handle, ffi.sizeof(v.ctype)))
		else
			fails = fails or {}
			table.insert(fails, string.format("%s: %s", v.name, ctsstr(v.ctype)))
		end
	end
	if fails then
		error(string.format("layout vars with non-unique ctype:\n\t%s", table.concat(fails, ",\n\t")))
	end
end

local function layouttab(M, tab)
	local newtab = {}
	for _,x in ipairs(tab) do
		local idx, slot = M:query(x.handle)
		if idx then
			x.idx = idx
			x.slot = slot
			table.insert(newtab, x)
		end
	end
	return newtab
end

local function layout(graph)
	guardcheck(graph)
	local M = graph.M
	checke(mut, M:layout())
	graph.groups = layouttab(M, graph.groups)
	graph.maps = layouttab(M, graph.maps)
	graph.vars = layouttab(M, graph.vars)
	graph.models = layouttab(M, graph.models)
	graph.guards = layouttab(M, graph.guards)
	typecheck(graph)
end

---- graph building ------------------------------

local function build(graph, alloc)
	return checkv(graph, graph.M:build(alloc and alloc(graph.M:size(), ffi.alignof("fhk_graph"))))
end

---- jump table ------------------------------

local function nametab(out, xs)
	for _,x in ipairs(xs) do
		out[x.idx] = x.name
	end
	return out
end

local function nametags(graph)
	return {
		node  = nametab(nametab(nametab({}, graph.vars), graph.models), graph.guards),
		map   = nametab({}, graph.maps),
		group = nametab({}, graph.groups)
	}
end

local function errfunc(graph)
	local tags = nametags(graph)
	return function(S)
		local err = ctypes.err(S.error)
		for k,tab in pairs(tags) do
			if err[k] and tab[err[k]] then
				err[k] = string.format("%s <%s>", tab[err[k]], err[k])
			end
		end
		error(tostring(err), 2)
	end
end

local function hole()
	error("tried to call hole in jump table")
end

local function ok() end

local function setjtab(J, tab)
	for _,x in ipairs(tab) do
		if x.slot then
			J[x.slot] = x.jfunc or hole
		end
	end
end

local function jtab(graph)
	graph.J[0] = errfunc(graph)
	graph.J[1] = ok
	setjtab(graph.J, graph.vars)
	setjtab(graph.J, graph.models)
	setjtab(graph.J, graph.groups)
	setjtab(graph.J, graph.maps)
end

---- func buffers ----------------------------------------

local function fbuf()
	return {
		src  = buffer.new(),
		upv  = {},
		name = nil,
	}
end

local function reset(fb)
	fb.src:reset()
	table.clear(fb.upv)
	fb.name = nil
end

local function upval(fb, v)
	local name = string.format("_%p", v)
	fb.upv[name] = v
	return name
end

---- code generation ----------------------------------------
-- variables that are always defined:
--     S  solver
--     X  parameter
--     C  ffi.C
-- for jfuncs only:
--     J  jump table

local function emit_upvdef(buf, upv)
	local uvals = {}
	for name, uv in pairs(upv) do
		buf:put(",", name)
		table.insert(uvals, uv)
	end
	return uvals
end

local function ffunc(graph, fb, sig)
	local buf = graph.buf:reset()
	buf:put("local C")
	local uvals = emit_upvdef(buf, fb.upv)
	buf:put("= ...\n")
	buf:putf("return function(%s)\n", sig or "S, X")
	buf:put(fb.src)
	buf:put("end\n")
	return load(buf, fb.name)(C, unpack(uvals))
end

local function emit_jfunc(graph, fb)
	local buf = graph.buf:reset()
	buf:put("local C, J")
	local uvals = emit_upvdef(buf, fb.upv)
	buf:put("= ...\n")
	buf:put("return function(S, X)\n")
	buf:put(fb.src)
	buf:put("\treturn J[C.fhk_continue(S)](S, X)\n")
	buf:put("end\n")
	return load(buf, fb.name)(C, graph.J, unpack(uvals))
end

local function jfunc(graph, x, fb)
	x.jfunc = emit_jfunc(graph, fb)
end

local function jump(graph)
	local fb = fbuf()
	fb.name = "=fhk: driver"
	return emit_jfunc(graph, fb)
end

local function funcname(f)
	local info = debug.getinfo(f, "S")
	return info.short_src:match("[^/]*$") .. ":" .. info.linedefined
end

local function xname(x)
	return x and x.name or "generic"
end

local function defidx(idx)
	return idx or "S.idx"
end

local function definst(inst)
	return inst or "S.inst"
end

---- vref/setvalue ----------------------------------------

local function intptr(x)
	return ffi.cast("intptr_t", ffi.cast("void *", x))
end

local function rt_setvalue_intptr(S, xi, ss, p)
	C.fhk_setvalue(S, xi, ss, ffi.cast("void *", p))
end

local function rt_setvalue_intptr_disp(S, xi, ss, p, disp)
	return rt_setvalue_intptr(S, xi, ss, intptr(p) + disp)
end

-- vref sparse pointer
--     f(inst, X)   pointer callback
--     offset?      offset from f(inst, X), default 0
--     var?         hardcoded variable
--     inst?        hardcoded instance
--
-- VREF idx, inst -> f(inst, X) + offset
local function vrefs(fb, op)
	local idx = defidx(op.var and op.var.idx)
	local inst = definst(op.inst)
	local f = upval(fb, checknil(op.f, "function is nil (vrefs: %s)", xname(op.var)))
	if (not op.offset) or op.offset == 0 then
		fb.src:putf("C.fhk_setvalue(S, %s, %s, %s(%s, X))\n", idx, inst, f, inst)
	else
		fb.upv.rt_setvalue_intptr_disp = rt_setvalue_intptr_disp
		fb.src:putf(
			"rt_setvalue_intptr_disp(S, %s, %s, %s(%s, X), %d)\n",
			idx, inst, f, inst, op.offset
		)
	end
	fb.name = string.format("=fhk:vrefs<%s>@%s+%d", xname(op.var), funcname(op.f), op.offset or 0)
end

-- vref dense pointer
--     f(inst, X)   pointer, subset callback
--     offset?      offset from pointer, default 0
--     var?         hardcoded variable
--     inst?        hardcoded instance
--
-- ptr, ss = f(inst, X)
-- VREF idx, ss -> ptr + offset
local function vrefd(fb, op)
	local idx = defidx(op.var and op.var.idx)
	local inst = definst(op.inst)
	local f = upval(fb, checknil(op.f, "function is nil (vrefd: %s)", xname(op.var)))
	fb.src:putf("local ptr, ss = %s(%s, X)\n", f, inst)
	if (not op.offset) or op.offset == 0 then
		fb.src:putf("C.fhk_setvalue(S, %s, ss, ptr)\n", idx)
	else
		fb.upv.rt_setvalue_intptr_disp = rt_setvalue_intptr_disp
		fb.src:putf("rt_setvalue_intptr_disp(S, %s, ss, ptr, %d)\n", idx, op.offset)
	end
	fb.name = string.format("=fhk:vrefd<%s>@%s+%d", xname(op.var), funcname(op.f), op.offset or 0)
end

-- vref constant pointer
--     ptr        pointer (you must ensure it lives as long as the driver)
--     var?       hardcoded variable
--     ss?        hardcoded subset
--
-- VREF idx, ss|inst -> ptr
local function vrefk(fb, op)
	local idx = defidx(op.var and op.var.idx)
	local ptr = ffi.cast("intptr_t", op.ptr)
	fb.upv.rt_setvalue_intptr = rt_setvalue_intptr
	if op.ss then
		fb.src:putf("rt_setvalue_intptr(S, %s, 0x%xLL, 0x%xLL)", idx, op.ss, ptr)
	else
		fb.src:putf("rt_setvalue_intptr(S, %s, S.inst, 0x%xLL)", idx, ptr)
	end
	fb.name = string.format("=fhk:vrefk<%s>@0x%x", xname(op.var), ptr)
end

-- vref value
--     f(inst, X)   value callback
--     ctype?       value ctype
--     var?         hardcoded variable
--     inst?        hardcoded inst
--
-- ctype value[1]
-- value[0] <- f(inst, X)
-- VREF idx, ss -> value
local function vrefv(fb, op)
	local idx = defidx(op.var and op.var.idx)
	local inst = definst(op.inst)
	local f = upval(fb, checknil(op.f, "function is nil (vrefv: %s)", xname(op.var)))
	local ctp = upval(fb, ffi.typeof("$*", op.var and op.var.ctype or op.ctype))
	fb.upv.cast = ffi.cast
	fb.src:putf(
		"cast(%s, C.fhk_setvalueD(S, %s, %s))[0] = %s(%s, X)\n",
		ctp, idx, inst, f, inst
	)
	fb.name = string.format("=fhk:vrefv<%s>@%s", xname(op.var), funcname(op.f))
end

---- mapcall/setmap ----------------------------------------

-- setmapk function
--     f(X)      subset callback
--     map?      hardcoded map
--
-- MAPCALLK idx -> f(X)
local function mapcallkf(fb, op)
	local idx = defidx(op.map and op.map.idx)
	local f = upval(fb, checknil(op.f, "function is nil (mapcall: %s)", xname(op.map)))
	fb.src:putf("C.fhk_setmapK(S, %s, %s(X))\n", idx, f)
	fb.name = string.format("=fhk:mapcallkf<%s>@%s", xname(op.map), funcname(op.f))
end

-- setmapi function
--     f(inst, X)   subset callback
--     map?         hardcoded map
--     inst?        hardcoded inst
--
-- MAPCALLI idx, inst -> f(inst, X)
local function mapcallif(fb, op)
	local idx = defidx(op.map and op.map.idx)
	local inst = definst(op.inst)
	local f = upval(fb, checknil(op.f, "function is nil (mapcall: %s)", xname(op.map)))
	fb.src:putf("C.fhk_setmapI(S, %s, %s, %s(%s, X))\n", idx, inst, f, inst)
	fb.name = string.format("=fhk:mapcallif<%s>@%s", xname(op.map), funcname(op.f))
end

-- generic lua function mapcall.
--     f([inst,] X) subset callback
--     map          hardcoded map
--     inst?        hardcoded inst
local function mapcallf(fb, op)
	if op.map.flags:match("i") then
		mapcallif(fb, op)
	else
		mapcallkf(fb, op)
	end
end

---- model calls ----------------------------------------
-- signatures: ssvv:s -> scalar scalar vector vector => scalar

local function cedge_inext(e, i)
	i = i+1
	if i < e.n then
		return i, e.p[i]
	end
end

local cedge_mt = {
	__index = function(self, i)
		return self.p[i]
	end,

	__newindex = function(self, i, v)
		self.p[i] = v
	end,

	__len = function(self)
		return tonumber(self.n)
	end,

	__ipairs = function(self)
		return cedge_inext, self, -1
	end,

	__tostring = function(self)
		local buf = {}
		for _,v in ipairs(self) do
			table.insert(buf, tostring(v))
		end
		return string.format("[%s]", table.concat(buf, ", "))
	end
}

local function cedge_ct_new(ctype)
	return ffi.metatype(
		ffi.typeof([[
			struct {
				$ *p;
				size_t n;
			}
		]], ctype),
		cedge_mt
	)
end

local cedge_cts = {}
local function edgect(ctype)
	local ctid = tonumber(ctype)
	if not cedge_cts[ctid] then
		cedge_cts[ctid] = cedge_ct_new(ctype)
	end
	return cedge_cts[ctid]
end

local function edgerank(e)
	return e.rank or e.map2.flags:match("[sv]")
end

local function edgeranksig(sig, i)
	if sig then
		local s = sig:sub(i,i)
		if s:match("[sv]") then
			return s
		end
	end
end

local function sigrank(model, sig)
	local idx = 1
	local params, returns = {}, {}
	for i,p in ipairs(model.params) do
		local rank = edgeranksig(sig, idx) or edgerank(p)
		if not rank then
			error(string.format("failed to infer signature: param(#%d): %s->%s", i, model.name, p.var.name))
		end
		table.insert(params, rank)
		idx = idx+1
	end
	idx = idx+1 -- skip ':'
	for i,r in ipairs(model.returns) do
		local rank = edgeranksig(sig, idx) or edgerank(r)
		if not rank then
			error(string.format("failed to infer signature: return(#%d): %s->%s", i, model.name, r.var.name))
		end
		table.insert(returns, rank)
		idx = idx+1
	end
	return params, returns
end

local function sigct(model)
	local buf = buffer.new()
	buf:put("struct {\n")
	local cts = {}
	for i,p in ipairs(model.params) do
		buf:putf("$ param%d;\n", i)
		table.insert(cts, edgect(p.var.ctype))
	end
	for i,r in ipairs(model.returns) do
		buf:putf("$ return%d;\n", i)
		table.insert(cts, edgect(r.var.ctype))
	end
	buf:put("}")
	return ffi.typeof(tostring(buf), unpack(cts))
end

local function cache(f)
	local cache = setmetatable({}, {
		__mode = "v",
		__index = function(self, ctid)
			self[ctid] = f()
			return self[ctid]
		end
	})
	return function(ctid)
		return cache[ctid]
	end
end

local convctab_func = cache(function()
	return load([[
		local new = ...
		return function(edge)
			local out = new(#edge, 0)
			for i=0, #edge-1 do
				out[i+1] = edge.p[i]
			end
			return out
		end
	]])(table.new)
end)

local convtabc_func = cache(function()
	return load([[
		return function(edge, tab)
			for i=0, #edge-1 do
				edge.p[i] = tab[i+1]
			end
		end
	]])()
end)

-- modcall lua function w/ lua table conversion
--     model        hardcoded model
--     f            lua function
--     signature?   scalar/vector signature
--
-- MODCALL r1, r2, .., rN <- f(p1, p2, ..., pM)
local function modcalllua(fb, op)
	local params, returns, conv = {}, {}, {}
	local sigp, sigr = sigrank(op.model, op.signature)
	for i,r in ipairs(op.model.returns) do
		if sigr[i] == "s" then
			returns[i] = string.format("call.return%d[0]", i)
		else
			fb.src:putf("local return%d\n", i)
			returns[i] = string.format("return%d", i)
			local ctid = tonumber(r.var.ctype)
			fb.upv[string.format("convtabc%d", ctid)] = convtabc_func(ctid)
			table.insert(conv, string.format("convtabc%d(call.return%d,return%d)", ctid, i, i))
		end
	end
	for i,p in ipairs(op.model.params) do
		if sigp[i] == "s" then
			params[i] = string.format("call.param%d[0]", i)
		else
			local ctid = tonumber(p.var.ctype)
			fb.upv[string.format("convctab%d", ctid)] = convctab_func(ctid)
			params[i] = string.format("convctab%d(call.param%d)", ctid, i)
		end
	end
	local f = upval(fb, checknil(op.f, "function is nil (modcalllua: %s)", op.model.name))
	local ct = upval(fb, ffi.typeof("$*", sigct(op.model)))
	fb.upv.cast = ffi.cast
	fb.src:putf("local call = cast(%s, S.edges)\n", ct)
	fb.src:putf("%s = %s(%s)\n", table.concat(returns, ","), f, table.concat(params, ","))
	fb.src:putf("%s\n", table.concat(conv, "\n"))
	fb.name = string.format("=fhk:modcalllua<%s>@%s", op.model.name, funcname(op.f))
end

-- modcall lua function w/ ffi structs
--     model        hardcoded model
--     f            lua function
--     signature?   scalar/vector signature
--
-- MODCALL rs1, rs2, .., rsN <- f(p1, p2, ..., pM, rv1, rv2, ..., rvL)
local function modcallffi(fb, op)
	local params, returns = {}, {}
	local sigp, sigr = sigrank(op.model, op.signature)
	for i,s in ipairs(sigp) do
		if s == "s" then
			table.insert(params, string.format("call.param%d[0]", i))
		else
			table.insert(params, string.format("call.param%d", i))
		end
	end
	for i,s in ipairs(sigr) do
		if s == "s" then
			table.insert(returns, string.format("call.return%d[0]", i))
		else
			table.insert(params, string.format("call.return%d", i))
		end
	end
	local f = upval(fb, checknil(op.f, "function is nil (modcallffi: %s)", op.model.name))
	local ct = upval(fb, ffi.typeof("$*", sigct(op.model)))
	fb.upv.cast = ffi.cast
	fb.src:putf("local call = cast(%s, S.edges)\n", ct)
	if #returns > 0 then
		fb.src:putf("%s = ", table.concat(returns, ", "))
	end
	fb.src:putf("%s(%s)", f, table.concat(params, ", "))
	fb.name = string.format("=fhk:modcallffi<%s>@%s", op.model.name, funcname(op.f))
end

-- modcall lua expression (template)
--     model        hardcoded model
--     expr         template
local function modcallexpr(fb, op)
	fb.upv.cast = ffi.cast
	local ct = upval(fb, ffi.typeof("$*", sigct(op.model)))
	fb.src:putf("local call = cast(%s, S.edges)\n", ct)
	local comma = ""
	for i=1, #op.model.returns do
		fb.src:putf("call.return%d[0]", i)
		fb.src:put(comma)
		comma = ","
	end
	fb.src:put(" = ", (op.expr:gsub("%$(%d+)", function(i) return string.format("call.param%d[0]", i) end)))
	fb.src:put("\n")
	fb.name = string.format("=fhk:modcallexpr<%s>", op.expr)
end

-- modcall const value
--     model        hardcoded model
--     value        constant table, one for each return edge
--                  primitive -> broadcast
--                  table     -> copy
--                  pointer   -> copy
--
-- MODCALL r1,r2,...,rN <- const
local function modcallconst(fb, op)
	local ct = upval(fb, ffi.typeof("$*", sigct(op.model)))
	fb.upv.cast = ffi.cast
	fb.src:putf("local call = cast(%s, S.edges)\n", ct)

	for i,r in ipairs(op.model.returns) do
		local v
		if type(op.value) == "table" then
			v = op.value[i]
		else
			v = op.value
		end

		if type(v) == "number" then
			fb.src:putf("for i=0, #call.return%d-1 do call.return%d[i] = %s end\n", i, i, v)
		else
			if type(v) == "table" then
				v = ffi.new(ffi.typeof("$[?]", r.var.ctype), #v, v)
			end
			local ptr = upval(fb, v)
			fb.upv.copy = ffi.copy
			fb.src:putf(
				"copy(call.return%d.p, %s, call.return%d.n*%d)\n",
				i, ptr, i, ffi.sizeof(r.var.ctype)
			)
		end
	end

	fb.name = string.format("=fhk:modcallconst<%s>", op.model.name)
end

---- modcall loaders ----------------------------------------

local loaders = {}

-- Lua(function [, signature])
-- Lua(module, name, [name, ...])
local function loadlua(a,...)
	if type(a) == "string" then
		local x = require(a)
		for _,k in ipairs({...}) do
			if not x then break end
			x = x[k]
		end
		return x
	else
		return a, ...
	end
end

function loaders.Lua(fb, model, ...)
	local func, sig = loadlua(...)
	modcalllua(fb, {model=model, f=func, signature=sig})
end

function loaders.LuaJIT(fb, model, ...)
	local func, sig = loadlua(...)
	modcallffi(fb, {model=model, f=func, signature=sig})
end

function loaders.Expr(fb, model, expr)
	modcallexpr(fb, {model=model, expr=expr})
end

function loaders.Const(fb, model, value)
	modcallconst(fb, {model=model, value=value})
end

local function loadlang(lang)
	local loader = loaders[lang]
	local err
	if not loader then
		local ok, x = pcall(require, "fhk_lang_"..lang)
		if ok then
			if x.load then
				loader = x.load
			else
				err = "lang module didn't export a `load' function."
			end
		else
			err = x
		end
	end
	return loader, err
end

---- setshape ----------------------------------------

local function checkshape(got, expected)
	error(string.format("shape functions disagree: %s ~= %s)", got, expected), 2)
end

-- setshape
--     value      function -> call to get shape
--                number -> hardcode
--                table -> assert all indiced equal and set shape
--     group?     hardcoded group
--
-- SHAPE idx -> value
local function setshape(fb, op)
	local idx = defidx(op.group and op.group.idx)
	local value = op.value
	if type(value) ~= "table" then
		value = {value}
	end
	if #value == 0 then
		error("empty setshape table")
	end
	local funcs = {}
	local k
	for _,x in ipairs(value) do
		if type(x) == "number" then
			if k then
				if x ~= k then
					error(string.format("setshape constants disagree: %d ~= %d", k, x))
				end
			else
				k = x
				fb.src:putf("C.fhk_setshape(S, %s, %d)\n", idx, k)
			end
		else
			table.insert(funcs, x)
		end
	end
	if #funcs > 0 then
		fb.upv.checkshape = checkshape
		if k then
			for _,func in ipairs(funcs) do
				fb.src:putf("checkshape(%s(X), %d)\n", upval(fb, func), k)
			end
		else
			fb.src:putf("local _shape = %s(X)\n", upval(fb, funcs[1]))
			for i=2, #funcs do
				fb.src:putf("checkshape(%s(X), _shape)\n", upval(fb, funcs[i]))
			end
			fb.src:putf("C.fhk_setshape(S, %s, _shape)\n", idx)
		end
	end
	fb.name = string.format("=fhk:setshape<%s>", xname(op.group))
end

---- trap ----------------------------------------

-- trap
--    mes      error message
local function trap(fb, op)
	fb.upv.error = error
	fb.upv.mes = string.format("TRAP -- %s", op.mes)
	fb.src:putf("error(mes)\n")
end

---- hook ----------------------------------------

-- hook
--     f    callback
local function hook(fb, op)
	local f = upval(fb, op.f)
	fb.src:putf("%s(S, X)\n", f)
end

--------------------------------------------------------------------------------

return {
	graph        = graph,
	ident        = ident,
	space        = space,
	only         = only,
	addgroup     = addgroup,
	addmap       = addmap,
	umap2        = umap2,
	addmodel     = addmodel,
	setcost      = setcost,
	setctype     = setctype,
	addvar       = addvar,
	setop        = setop,
	addguard     = addguard,
	addparam     = addparam,
	addreturn    = addreturn,
	addcheck     = addcheck,
	setrank      = setrank,
	pin          = pin,
	prune        = prune,
	layout       = layout,
	build        = build,
	jtab         = jtab,
	fbuf         = fbuf,
	reset        = reset,
	upval        = upval,
	ffunc        = ffunc,
	jfunc        = jfunc,
	jump         = jump,
	defidx       = defidx,
	definst      = definst,
	vrefs        = vrefs,
	vrefd        = vrefd,
	vrefk        = vrefk,
	vrefv        = vrefv,
	mapcallkf    = mapcallkf,
	mapcallif    = mapcallif,
	mapcallf     = mapcallf,
	sigrank      = sigrank,
	sigct        = sigct,
	modcalllua   = modcalllua,
	modcallffi   = modcallffi,
	modcallexpr  = modcallexpr,
	modcallconst = modcallconst,
	loadlang     = loadlang,
	setshape     = setshape,
	trap         = trap,
	hook         = hook
}
