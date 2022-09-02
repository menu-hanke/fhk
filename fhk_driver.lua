local cdef = require "fhk_cdef"
local ctypes = require "fhk_ctypes"
local C = require "fhk_clib"
local buffer = require "string.buffer"
local ffi = require "ffi"
require "table.clear"
require "table.new"

---- lookups ----------------------------------------

-- group#name  -->  group, name
-- name        -->  nil, name
local function xsplitname(name)
	local g, n = name:match("^(.-)#(.*)$")
	if g then return g, n end
	return nil, name
end

-- group#name  -->  group, name
-- name        -->  global, name
local function splitname(name)
	local g, n = xsplitname(name)
	if g then return g, n end
	return "global", name
end

local function joinname(group, name)
	local gg, gname = xsplitname(group)
	if gg and gg ~= "global" then
		error(string.format("non-global group: %s", gname))
	end
	return gname.."#"..name
end

-- group#name  --> group#name
-- name        --> global#name
local function canon(name)
	if name:match("#") then
		return name
	else
		return joinname("global", name)
	end
end

local function keyv(name)
	return "V;"..name
end

local function keym(name)
	return "M;"..name
end

---- queries & error handling ----------------------------------------

local function desc(obj)
	-- TODO: something better here
	return obj.name
end

local function patcherror(graph, e)
	if e.handle and graph.objs[e.handle] then
		e.handle = desc(graph.objs[e.handle])
	end
	return e
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

---- debug/inspect ----------------------------------------

local tagchar = "VMXDCPR"
local tagmask = "mgpdsjrx"

local function objcolor(cobj)
	if bit.band(cobj.tag, cdef.mtagmask.s) ~= 0 then return 31 end
	if cobj.what == "var" then return 36 end
	if cobj.what == "model" then return 33 end
	return ""
end

local function costcolor(cost)
	if cost == math.huge then return 31 end
	if cost == 0 then return 32 end
	return ""
end

local function dumpcost(buf, cost, color)
	if color then buf:put("\027[", costcolor(cost), "m") end
	local num = #buf
	buf:put(cost)
	num = #buf - num
	if color then buf:put("\027[m") end
	return num
end

local function dumpidx(buf, idx, color)
	if color then buf:put("\027[34m") end
	buf:putf("%04d", idx)
	if color then buf:put("\027[m") end
end

local function dumpobj(graph, buf, handle, cobj, color)
	local obj = graph.objs[handle]
	buf:putf("0x%04x ", handle)
	if obj and obj.idx then
		dumpidx(buf, obj.idx, color)
	else
		buf:put((" "):rep(4))
	end
	buf:put(" ")
	if color then buf:put("\027[", objcolor(cobj), "m") end
	local tag = cobj.tag
	local typ = bit.band(tag, cdef.mtagmask.T)
	buf:putf(tagchar:sub(typ+1,typ+1))
	for i=1, #tagmask do
		local c = tagmask:sub(i,i)
		buf:put(bit.band(tag, cdef.mtagmask[c]) == 0 and "-" or c)
	end
	if color then buf:put("\027[m") end
	buf:putf(" %-15s ", obj and obj.name or "")
	if bit.band(tag, cdef.mtagmask.s) ~= 0 then return end
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
		local ct = tostring(obj.ctype):match("ctype<([^>]+)>")
		if color then buf:put("\027[35m") end
		buf:putf(" %-9s", ct)
		if color then buf:put("\027[m") end
	else
		buf:put((" "):rep(10))
	end
	if obj and obj.jump then
		buf:put("->")
		dumpidx(buf, obj.jump, color)
		if obj.impl then
			buf:put(" ", tostring(obj.impl.loader))
		end
	end
end

local function graph_dump(graph, color)
	local buf = buffer.new()
	for h,o in graph.M:opairs() do
		if o.what == "var" or o.what == "model" then
			dumpobj(graph, buf, h, o, color)
			buf:put("\n")
		end
	end
	return buf:get()
end

---- building ----------------------------------------

local function graph_setname(graph, obj, name)
	if obj.name then
		if obj.name == name then return end
		error(string.format("rename object: %s -> %s", obj.name, name))
	end
	obj.name = name
	if cdef.debug then
		C.fhk_mut_set_sym(graph.M, obj.handle, name)
	end
	local o = graph.M:get(obj.handle)
	if o.what == "var" then
		graph.lookup[keyv(name)] = obj
	elseif o.what == "model" then
		graph.lookup[keym(name)] = obj
	end
end

local graph_addvar

local function graph_getvar(graph, name)
	if type(name) ~= "string" then return name end
	name = canon(name)
	local var = graph.lookup[keyv(name)]
	if not var then
		var = graph_addvar(graph, splitname(name))
		graph_setname(graph, var, name)
	end
	return var
end

graph_addvar = function(graph, group)
	group = graph_getvar(graph, group)
	local handle = checkv(graph, graph.M:add_var(group.handle))
	local var = {handle=handle, group=group}
	graph.objs[handle] = var
	return var
end

local function graph_setinverse(graph, var, inverse)
	var = graph_getvar(graph, var)
	inverse = graph_getvar(graph, inverse)
	checke(graph, graph.M:set_inverse(var.handle, inverse.handle))
end

local function graph_setlhs(graph, guard, var)
	checke(graph, graph.M:set_lhs(guard.handle, var.handle))
	guard.lhs = var
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
		elseif x[0] == true then
			-- already sorted.
			return x
		else
			local out = { [0]=true }
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
	local C = { [0]=true }
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

-- obj :: var|edge
local function setcts(obj, cts)
	obj.ctype = ctintersect(ctids(obj.ctype), ctids(cts))
end

local function graph_addmodel(graph, group)
	group = graph_getvar(graph, group)
	local handle = checkv(graph, graph.M:add_model(group.handle))
	local model = {
		handle  = handle,
		group   = group,
		params  = {},
		returns = {},
	}
	graph.objs[handle] = model
	return model
end

local function graph_getmodel(graph, name)
	if type(name) ~= "string" then return name end
	name = canon(name)
	local mod = graph.lookup[keym(name)]
	if not mod then
		mod = graph_addmodel(graph, splitname(name))
		graph_setname(graph, mod, name)
	end
	return mod
end

local function graph_setcost(graph, model, k, c)
	graph.M:set_cost(graph_getmodel(graph, model).handle, k, c)
end

local function graph_getedgevar(graph, model, var)
	if type(var) ~= "string" then return var end
	-- global/ident may appear ungrouped
	local v = graph.lookup[keyv(var)]
	if v then return v end
	local group = xsplitname(var)
	if group then
		return graph_getvar(graph, var)
	else
		-- TODO: this could be resolved by keying the variables with something
		-- that doesn't contain the group's name.
		-- but this situation probably doesn't happen much in practice anyway.
		if not model.group.name then
			error(string.format(
				"ungrouped variable reference from unnamed group (model: %s variable: %s)",
				desc(model), var
			))
		end
		return graph_getvar(graph, joinname(model.group.name, var))
	end
end

local function graph_getedgemap(graph, model, var, map)
	-- shorthand space
	if map == "*" then return var.group end
	-- non-default map
	if map then return graph_getedgevar(graph, model, map) end
	-- same group: default to ident
	if model.group == var.group then return graph.ident end
	-- var is global: default to global
	if var.group == graph.global then return graph.global end
	-- model is global: default to space
	if model.group == graph.global then return var.group end
	-- both non-global, different groups: create default map
	if not (model.group.name and var.group.name) then
		error(string.format(
			"default map between anonymous groups (%s, %s)",
			desc(model.group), desc(var.group)
		))
	end
	local _, mgroup = xsplitname(model.group.name)
	local _, vgroup = xsplitname(var.group.name)
	local name = joinname(mgroup, "->"..vgroup)
	map = graph.lookup[keyv(name)]
	if not map then
		map = graph_getvar(graph, name)
		local inv = graph_getvar(graph, joinname(vgroup, "->"..mgroup))
		graph_setinverse(graph, map, inv)
	end
	return map
end

local function graph_addparam(graph, model, var, map)
	model = graph_getmodel(graph, model)
	var = graph_getedgevar(graph, model, var)
	map = graph_getedgemap(graph, model, var, map)
	local handle = checkv(graph, graph.M:add_param(model.handle, var.handle, map.handle))
	local edge = {
		handle = handle,
		var    = var,
		map    = map
	}
	table.insert(model.params, edge)
	graph.objs[handle] = edge
	return edge
end

local function graph_addreturn(graph, model, var, map)
	model = graph_getmodel(graph, model)
	var = graph_getedgevar(graph, model, var)
	var.computed = true
	map = graph_getedgemap(graph, model, var, map)
	local handle = checkv(graph, graph.M:add_return(model.handle, var.handle, map.handle))
	local edge = {
		handle = handle,
		var    = var,
		map    = map
	}
	table.insert(model.returns, edge)
	graph.objs[handle] = edge
	return edge
end

local function graph_addcheck(graph, model, guard, map, penalty)
	model = graph_getmodel(graph, model)
	guard = graph_getedgevar(graph, model, guard)
	map = graph_getedgemap(graph, model, guard, map)
	checkv(graph, graph.M:add_check(model.handle, guard.handle, map.handle, penalty))
end

local function graph_addrcheck(graph, edge, check, penalty)
	checkv(graph, graph.M:add_rcheck(edge.handle, check.handle, penalty))
end

-- addpredicate(graph [, operator, rhs])
local function graph_addpredicate(graph, operator, rhs)
	local handle = checkv(graph, graph.M:add_predicate())
	return {handle=handle, operator=operator, rhs=rhs}
end

local function graph_setpredicate(graph, obj, pre)
	checke(graph, graph.M:set_predicate(obj.handle, pre.handle))
	obj.predicate = pre
end

local function setimpl(obj, impl)
	obj.impl = impl
end

local function setlazy(obj)
	error("TODO")
end

-- mode = "s"|"v" (scalar/vector)
-- this can be set on, from highest to lowest priority:
--   models -> applies to all edges pointing from that model
--   edges  -> applies to only that edge
--   maps   -> applies to all edges with that map
--   vars   -> applies to all edges pointing to that variable
local function setmode(obj, mode)
	obj.mode = mode
end

local function _getmode(edges, buf)
	for _,e in ipairs(edges) do
		buf:put(e.mode or e.map.mode or e.var.mode or ".")
	end
end

-- s -> scalar
-- v -> vector
-- . -> any
local function getmode(model)
	if model.mode then
		return #model.mode == 1 and model.mode:rep(#model.params+#model.returns) or model.mode
	end
	local buf = buffer.new()
	_getmode(model.params, buf)
	_getmode(model.returns, buf)
	return tostring(buf)
end

local function overridemode(a, b)
	if not (a and b) then return a or b end
	local buf = buffer.new()
	for i=1, #a do
		buf:put(b:sub(i,i) == "." and a:sub(i,i) or b:sub(i,i))
	end
	return tostring(buf)
end

---- codegen ----------------------------------------

local function code_upval(code, v)
	if type(v) == "number" then
		return tostring(v)
	else
		local name = string.format("_%p", v)
		code.upv[name] = v
		return name
	end
end

local function emitupvals(code, buf)
	buf:put("local ")
	local uval = {}
	local comma = ""
	for name, uv in pairs(code.upv) do
		buf:put(comma, name)
		table.insert(uval, uv)
		comma = ", "
	end
	if comma == "" then
		-- no upvalues
		buf:reset()
	else
		buf:put(" = ...\n")
	end
	return uval
end

local function code_emit(code, buf)
	buf = buf or buffer.new()
	local uval = emitupvals(code, buf)
	buf:put(code.src)
	return assert(load(buf, code.name))(unpack(uval))
end

local function code_emitjmp(code, J, buf)
	buf = buf or buffer.new()
	code.upv.J = J
	code.upv.C = C
	local uval = emitupvals(code, buf)
	buf:put("return function(S, X)\n")
	buf:put(code.src)
	buf:put("return J[C.fhk_continue(S)](S, X)\n")
	buf:put("end\n")
	return assert(load(buf, code.name))(unpack(uval))
end

local code_mt = {
	__index = {
		upval   = code_upval,
		emit    = code_emit,
		emitjmp = code_emitjmp
	}
}

local function code()
	return setmetatable({
		src  = buffer.new(),
		name = nil,
		upv  = {}
	}, code_mt)
end

local function funcname(f)
	local info = debug.getinfo(f, "S")
	return info.short_src:match("[^/]*$") .. ":" .. info.linedefined
end

---- variable opcodes ----------------------------------------
-- TODO(?): index-independent functions. when does this make sense? does this ever make sense?
-- we probably don't want different variables to become the same root trace since they
-- ultimately will have a different chain anyway?

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
--
-- VREF idx, inst -> f(inst, X) + offset
local function vrefs(J, o)
	local code = code()
	local offset = o.impl.offset
	local fv = code:upval(o.impl.f)
	if (not offset) or offset == 0 then
		code.src:putf("C.fhk_setvalue(S, S.idx, S.inst, %s(S.inst, X))\n", fv)
	else
		code.upv.rt_setvalue_intptr_disp = rt_setvalue_intptr_disp
		code.src:putf("rt_setvalue_intptr_disp(S, S.idx, S.inst, %s(S.inst, X), %d)\n", fv, offset)
	end
	code.name = string.format("=fhk:vrefs<%s>@%s+%d", desc(o), funcname(o.impl.f), offset or 0)
	return code:emitjmp(J)
end

-- vref dense pointer
--     f(inst, X)   pointer, subset callback
--     offset?      offset from pointer, default 0
--
-- ptr, ss = f(inst, X)
-- VREF idx, ss -> ptr + offset
local function vrefd(J, o)
	local code = code()
	local offset = o.impl.offset
	code.src:putf("local ptr, ss = %s(S.inst, X)\n", code:upval(o.impl.f))
	if (not offset) or offset == 0 then
		code.src:put("C.fhk_setvalue(S, S.idx, ss, ptr)\n")
	else
		code.upv.rt_setvalue_intptr_disp = rt_setvalue_intptr_disp
		code.src:putf("rt_setvalue_intptr_disp(S, S.idx, ss, ptr, %d)\n", offset)
	end
	code.name = string.format("=fhk:vrefd<%s>@%s+%d", desc(o), funcname(o.impl.f), offset or 0)
	return code:emitjmp(J)
end

-- vref constant pointer
--     ptr        pointer (you must ensure it lives as long as the driver)
--     ss?        hardcoded subset
--
-- VREF idx, ss|inst -> ptr
local function vrefk(J, o)
	local code = code()
	local ptr = ffi.cast("intptr_t", o.impl.ptr)
	code.upv.rt_setvalue_intptr = rt_setvalue_intptr
	if o.impl.ss then
		code.src:putf("rt_setvalue_intptr(S, S.idx, 0x%xLL, 0x%xLL)", o.impl.ss, ptr)
	else
		code.src:putf("rt_setvalue_intptr(S, S.idx, S.inst, 0x%xLL)", ptr)
	end
	code.name = string.format("=fhk:vrefk<%s>@0x%x", desc(o), ptr)
	return code:emitjmp(J)
end

-- vref value
--     f(inst, X)   value callback
--     ctype?       value ctype
--
-- ctype value[1]
-- value[0] <- f(inst, X)
-- VREF idx, inst -> value
local function vrefv(J, o)
	local code = code()
	local ctp = code:upval(ffi.typeof("$*", o.impl.ctype or o.ctype))
	code.upv.cast = ffi.cast
	code.src:putf(
		"cast(%s, C.fhk_setvalueD(S, S.idx, S.inst))[0] = %s(S.inst, X)\n",
		ctp, code:upval(o.impl.f)
	)
	code.name = string.format("=fhk:vrefv<%s>@%s", desc(o), funcname(o.impl.f))
	return code:emitjmp(J)
end

local builtins = {
	vrefs = vrefs,
	vrefd = vrefd,
	vrefk = vrefk,
	vrefv = vrefv
}

---- declarative api (g-files) ----------------------------------------

local overlay_mt = { __index = function(self, key) return self[-1][key] end }
local function overlay(tab) return setmetatable({[-1]=tab}, overlay_mt) end
local function prev(overlay) return overlay[-1] end

local function setk(k)
	return function(v)
		return function(x)
			x[k] = v
		end
	end
end

local settag    = setk "tag"
local setparam  = settag "param"
local setreturn = settag "return"
local setcheck  = settag "check"
local function params(...) return {apply=setparam, ...} end
local function returns(...) return {apply=setreturn, ...} end
local function check(...) return {apply=setcheck, ...} end
local function cost(kc) return {tag="cost", k=kc.k, c=kc.c} end
local costderive = cost {k=0, c=1}
local function ctype(ct) return {tag="ctype", ctype=ct} end
local function inverse(var) return {tag="inverse", inverse=var} end

local virtual_mt = {
	__index = { tag="virtual" },
	__call = function(self, v)
		for _,f in ipairs(self) do
			f(v)
		end
	end
}
local function virtual(...)
	return setmetatable({...}, virtual_mt)
end

local function virtualgroup(group, virt)
	return function(v)
		if v.group == group then
			return virt(v)
		end
	end
end

local infix_mt
local function isinfix(x) return type(x) == "table" and x.infix end
local function infix(f) return setmetatable({f=f}, infix_mt) end
infix_mt = {
	__index = { infix=true },
	__mul = function(left, right)
		if isinfix(left) then
			if isinfix(right) then
				local f, g = left.f, right.f
				return infix(function(x) return g(f(x)) end)
			end
			return {apply=left.f, right}
		else
			return {apply=right.f, left}
		end
	end
}

local mode_mt = {
	__index = {tag="mode"},
	__mul = function(left, right)
		if type(left) == "table" and left.tag == "mode" then
			left, right = right, left
		end
		return {apply=function(x) x.mode=right.mode end, left}
	end
}
local function mode(m)
	return setmetatable({mode=m}, mode_mt)
end

local function checktab(x)
	return type(x) == "table" and x or {x}
end

local function tabf(f)
	return function(x)
		return f(checktab(x))
	end
end

local function infixmodifier(f)
	return function(...)
		return infix(f(...))
	end
end

local function setpredicate(operator)
	return function(rhs)
		return function(x)
			x.predicate = {operator=operator, rhs=rhs}
		end
	end
end

local as      = infixmodifier(setk "ctype")
local choose  = infixmodifier(setk "map")
local penalty = infixmodifier(setk "penalty")
local is      = infixmodifier(tabf(setpredicate "is"))
local is_not  = infixmodifier(tabf(setpredicate "isn"))
local gt      = infixmodifier(setpredicate ">")
local ge      = infixmodifier(setpredicate ">=")
local lt      = infixmodifier(setpredicate "<")
local le      = infixmodifier(setpredicate "<=")

local function newimpl(loader,  ...)
	local r = {loader=loader}
	for _,t in ipairs({...}) do
		if type(t) == "table" then
			for k,v in pairs(t) do
				if type(k) == "number" and k < #t then
					table.insert(r, v)
				else
					r[k] = v
				end
			end
		else
			table.insert(r, t)
		end
	end
	return r
end

local function impl(...)
	return {tag="impl", impl=newimpl(...)}
end

local impl_mt = {
	__call = function(_, ...) return impl(...) end,
	__index = function(self, loader)
		self[loader] = function(...) return impl(loader, ...) end
		return self[loader]
	end
}

local function decledge(state, var, map)
	map = map or state.map
	if state.tag == "check" then
		if state.predicate then
			local s = state
			while s do
				local predicate = rawget(s, "predicate")
				if predicate then
					table.insert(state.props, {tag="predck", var=var, map=map, predicate=predicate, penalty=s.penalty})
				end
				s = prev(s)
			end
		else
			table.insert(state.props, {tag="check", guard=var, map=map, penalty=state.penalty})
		end
	else
		table.insert(state.props, {tag=state.tag, var=var, map=map, ctype=state.ctype})
		if state.tag == "return" then
			if state.intrin then
				error("TODO: rchecks")
			end
		end
	end
end

local function normalize_modprops(props, state)
	if type(props) == "string" then
		local tok = props:gmatch("(~?)%s*([^~%s]+)")
		local sigil, name = tok()
		while sigil do
			if sigil ~= "" then error(string.format("unexpected sigil: %s", props)) end
			local x
			sigil, x = tok()
			if sigil == "~" then
				decledge(state, name, x)
				sigil, name = tok()
			else
				decledge(state, name)
				name = x
			end
		end
	elseif type(props) == "function" then
		table.insert(state.props, impl("Lua", props))
	elseif type(props) == "table" then
		if props.handle then
			decledge(state, props)
			return
		end
		if props.tag then
			table.insert(state.props, props)
			return
		end
		if props.apply then
			state = overlay(state)
			props.apply(state)
		end
		for _,x in ipairs(props) do
			normalize_modprops(x, state)
		end
	end
end

-- model "name" { ... }
-- model { ... }
local function model(graph, mod, ...)
	local props
	if type(mod) == "table" and not mod.handle then
		props = {mod, ...}
		mod = nil
	else
		props = {...}
		if type(mod) == "string" then
			mod = graph_getmodel(graph, mod)
		end
	end
	local norm = {}
	normalize_modprops(props, {tag="param", props=norm})
	if not mod then
		local group
		for _,p in ipairs(norm) do
			if p.tag == "return" then
				local g
				if type(p.var) == "string" then
					g = splitname(p.var)
					if g then
						g = graph_getvar(graph, g)
					end
				else
					g = p.var.group
				end
				if not group then
					group = g
				elseif g and g ~= group then
					error("no unique group for anonymous model")
				end
			end
		end
		mod = graph_addmodel(graph, group or "global")
	end
	for _,p in ipairs(norm) do
		local o
		if p.tag == "param" then
			o = graph_addparam(graph, mod, p.var, p.map)
		elseif p.tag == "return" then
			o = graph_addreturn(graph, mod, p.var, p.map)
		elseif p.tag == "predck" then
			local var = graph_getedgevar(graph, mod, p.var)
			local guard = graph_addvar(graph, var.group)
			graph_setlhs(graph, guard, var)
			graph_setpredicate(graph, guard, graph_addpredicate(graph, p.predicate.operator, p.predicate.rhs))
			graph_addcheck(graph, mod, guard, p.map, p.penalty)
		elseif p.tag == "check" then
			error("TODO: check->guard")
		elseif p.tag == "cost" then
			graph_setcost(graph, mod, p.k, p.c)
		elseif p.tag == "impl" then
			setimpl(mod, p.impl)
		end
		if p.ctype then
			setcts(o, p.ctype)
		end
	end
	return mod
end

local function derive(graph, ret, ...)
	local mod = model(graph, nil, returns(ret), costderive, ...)
	-- derives don't normally get names, but this makes debugging significantly easier.
	if cdef.debug then
		local sym = {}
		for _,r in ipairs(mod.returns) do
			if r.var.name then
				table.insert(sym, r.var.name)
			end
		end
		if #sym > 0 then
			C.fhk_mut_set_sym(graph.M, mod.handle, "derive["..table.concat(sym, ",").."]")
		end
	end
	return mod
end

local function normalize_varprops(props, out)
	if type(props) == "function" then
		table.insert(out, impl(vrefv, {f=props}))
	elseif type(props) == "cdata" or type(props) == "number" or (type(props) == "table" and props.typeid) then
		table.insert(out, {tag="ctype", ctype=props})
	elseif type(props) == "table" then
		if props.tag then
			table.insert(out, props)
			return
		end
		for _,x in ipairs(props) do
			normalize_varprops(x, out)
		end
	end
end

local function applyvar(graph, var, props)
	if type(var) == "table" and not var.handle then
		for _,v in ipairs(var) do
			applyvar(graph, v, props)
		end
	else
		var = graph_getvar(graph, var)
		for _,p in ipairs(props) do
			if p.tag == "impl" then
				setimpl(var, p.impl)
			elseif p.tag == "ctype" then
				setcts(var, p.ctype)
			elseif p.tag == "inverse" then
				graph_setinverse(graph, var, p.inverse)
			elseif p.tag == "mode" then
				setmode(var, p.mode)
			elseif p.tag == "virtual" then
				table.insert(graph.virt, virtualgroup(var, p))
			end
			-- TODO: meta prop?
		end
		return var
	end
end

-- var ("name"|handle|{vars}) { ... }
local function var(graph, var, ...)
	local props = {}
	normalize_varprops({...}, props)
	return applyvar(graph, var, props)
end

local function applylabel(graph, key, x)
	if type(x) == "table" then
		for k,v in pairs(x) do
			if type(k) == "number" then
				if type(v) == "function" then
					if key then
						local f = v
						v = function(l) return f(key.."."..l) end
					end
					table.insert(graph.label, v)
				elseif type(v) == "table" then
					applylabel(graph, key, v)
				end
			else
				applylabel(graph, key and (key.."."..k) or k, v)
			end
		end
	else
		graph.label[key] = x
	end
end

-- label (name|tab|func...)
local function label(graph, ...)
	applylabel(graph, nil, {...})
end

local function envread(env, fname)
	local f, err = loadfile(fname or error("read: expected file name"), nil, env)
	if not f then error(string.format("read: error (%s): %s", fname, err)) end
	return f()
end

local function envreadf(env)
	return function(f)
		if type(f) == "function" then
			return setfenv(f, env)()
		elseif type(f) == "string" then
			return envread(env, f)
		else
			error(string.format("unexpected parameter to read: %s", f))
		end
	end
end

local function env(graph)
	local env   = setmetatable({}, {__index=_G})
	env.read    = envreadf(env)
	env.model   = function(x) return function(...) return model(graph, x, ...) end end
	env.derive  = function(x) return function(...) return derive(graph, x, ...) end end
	env.var     = function(x)
		if type(x) == "function" or (type(x) == "table" and x.tag == "virtual") then
			table.insert(graph.virt, x)
		else
			return function(...) return var(graph, x, ...) end
		end
	end
	env.label   = function(...) return label(graph, ...) end
	env.virtual = virtual
	env.params  = params
	env.returns = returns
	env.check   = check
	env.cost    = cost
	env.ctype   = ctype
	env.inverse = inverse
	env.mode    = mode
	env.impl    = setmetatable({}, impl_mt)
	env.as      = as
	env.choose  = choose
	env.penalty = penalty
	env.is      = is
	env.is_not  = is_not
	env.gt      = gt
	env.ge      = ge
	env.lt      = lt
	env.le      = le
	return env
end

local function graph_read(graph, ...)
	local env = env(graph)
	for _,f in ipairs({...}) do
		env.read(f)
	end
	return env
end

---- analysis ----------------------------------------

local function impl_autoinverse(J)
	return function(S, X)
		C.fhk_invert(S.mem, S.edges[0].p, S.edges[0].n, S.edges[1].p, S.edges[1].n)
		return J[C.fhk_continue(S)](S, X)
	end
end

local function graph_completetopo(graph)
	-- complete variable info.
	-- this is the last step that may add objects to the graph.
	for h in graph.M:opairs("Ts=V") do
		local obj = graph.objs[h]
		for _,v in ipairs(graph.virt) do
			v(obj)
		end
	end
	-- blacklist all return edges that point to given variables.
	-- autocomplete inverse maps for non-group return edge maps that don't have inverses.
	for h in graph.M:opairs("Ts=R") do
		local edge = graph.objs[h]
		if edge.var.impl then
			graph.M:disable(h)
		elseif edge.map ~= edge.var.group and graph.M:get(edge.map.handle).inverse == 0 then
			graph_setinverse(graph, edge.map, graph_addvar(graph, edge.var.group))
		end
	end
	-- autocomplete inverses for maps that don't have a model or an impl, but do have an inverse.
	-- blacklist all other vars without either a model or an impl.
	for h,o in graph.M:opairs("Tsp=V") do
		local obj = graph.objs[h]
		if h > ctypes.mref_global and not (obj.computed or obj.impl) then
			if o.inverse ~= 0 and bit.band(o.tag, cdef.mtagmask.m) ~= 0 then
				local mod = graph_addmodel(graph, graph.global)
				graph_setcost(graph, mod, 0, 1)
				setimpl(mod, newimpl(impl_autoinverse))
				graph_addparam(graph, mod, graph.objs[o.inverse], graph.objs[o.inverse].group)
				graph_addreturn(graph, mod, obj, obj.group)
			else
				graph.M:disable(h)
			end
		end
	end
end

local function graph_analyze(graph)
	graph_completetopo(graph)
	checke(graph, graph.M:analyze())
end

local function graph_mark(graph, obj)
	checke(graph, graph.M:mark(obj.handle))
end

---- layout ----------------------------------------

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

local ctpref = {
	[cttoid "double"]  = 1, [cttoid "float"]    = 2,
	[cttoid "int8_t"]  = 3, [cttoid "uint8_t"]  = 4,
	[cttoid "int16_t"] = 5, [cttoid "uint16_t"] = 6,
	[cttoid "int32_t"] = 7, [cttoid "uint32_t"] = 8,
	[cttoid "int64_t"] = 9, [cttoid "uint64_t"] = 10,
	[cttoid "bool"]    = 11
}
local function selectctype(cts)
	if type(cts) == "table" then
		-- reflect ctype: unique choice
		if cts.typeid then return ctfromid(cts.typeid) end
		-- otherwise: pick the preferred one
		local ctid, pref = nil, math.huge
		for _,id in ipairs(cts) do
			local p = ctpref[id]
			if p and p < pref then
				ctid, pref = id, p
			end
		end
		ctid = ctid or cts[1]
		return ctid and ctfromid(ctid)
	elseif cts then
		-- unique choice: string/cdata/typeid
		return ctfromid(cttoid(cts))
	else
		-- cts=nil, ie. all types are possible.
		-- default to double.
		return ffi.typeof "double"
	end
end

local function hole(name)
	return function()
		error(string.format("missing jump table entry: %s", name))
	end
end

local function invalid()
	error("invalid jump table entry")
end

local function ok()
	-- nothing to do here. we are done.
end

local function graph_patchrhs(graph, x)
	if type(x) == "string" then
		return graph.label[x] or error(string.format("missing label reference: %s", x))
	end
	if type(x) == "table" then
		local tab = {}
		for i,v in ipairs(x) do
			tab[i] = graph_patchrhs(graph, v)
		end
		return tab
	end
	return x
end

local ctfp = { [0]=true, cttoid "float", cttoid "double" }
table.sort(ctfp)
local ctint = {
	[0]=true,
	cttoid "int8_t",  cttoid "uint8_t",
	cttoid "int16_t", cttoid "uint16_t",
	cttoid "int32_t", cttoid "uint32_t",
	cttoid "int64_t", cttoid "uint64_t"
}
table.sort(ctint)
local function pnum(predicate) return cdef.predicate[predicate] end
local predcts = {
	[">"] = ctfp, [">="] = ctfp, ["<"] = ctfp, ["<="] = ctfp,
	is = ctint, isn = ctint,
	[pnum "f32le"] = "float",  [pnum "f32ge"] = "float",
	[pnum "f64le"] = "double", [pnum "f64ge"] = "double",
	[pnum "isn"] = ctint
}

local nextafter = (function()
	local nextafter, nextafterf
	if jit.os == "Windows" then
		ffi.cdef [[
			float _nextafterf(float from, float to);
			double _nextafter(double from, double to);
		]]
		nextafter, nextafterf = "_nextafter", "_nextafterf"
	else
		ffi.cdef [[
			float nextafterf(float from, float to);
			double nextafter(double from, double to);
		]]
		nextafter, nextafterf = "nextafter", "nextafterf"
	end
	return function(from, to, ctid)
		if ctid == cttoid("double") then
			return ffi.C[nextafter](from, to)
		elseif ctid == cttoid("float") then
			return ffi.C[nextafterf](from, to)
		else
			error(string.format("non-fp ctype: %s", ct))
		end
	end
end)()

local function mask(x)
	if type(x) == "table" then
		local m = 0ULL
		for _,v in ipairs(x) do
			m = bit.bor(m, bit.lshift(1ULL, v))
		end
		return m
	else
		return x
	end
end

local function topredicate(operator, lhs, rhs)
	local ctid = cttoid(lhs)
	if operator == ">" then
		operator, rhs = ">=", nextafter(rhs, math.huge, ctid)
	elseif operator == "<" then
		operator, rhs = "<=", nextafter(rhs, -math.huge, ctid)
	elseif operator == "is" then
		operator, rhs = "isn", bit.bnot(mask(rhs))
	elseif operator == "isn" then
		rhs = mask(rhs)
	end
	if operator == ">=" or operator == "<=" then
		local fp32 = ctid == cttoid "float"
		operator = fp32 and (operator == ">=" and "f32ge" or "f32le")
			or (operator == ">=" and "f64ge" or "f64le")
	end
	if type(operator) == "string" then
		operator = cdef.predicate[operator]
	end
	local crhs = ffi.new("fhk_operand[1]")
	ffi.cast(ffi.typeof("$*", lhs), crhs)[0] = rhs
	return operator, crhs
end

local function graph_typing(graph)
	-- TODO (?): this step could use type hints from model impls, eg. python.
	-- propagate type info from selected edges.
	-- the edge type mask is an assertion, and if we can't honor it we won't build the graph.
	for h,o in graph.M:opairs("r") do
		if o.what == "edge" then
			local obj = graph.objs[h]
			setcts(obj.var, obj.ctype)
		end
	end
	-- all maps must be typed fhk_subset.
	local subsetct = tonumber(ffi.typeof("fhk_subset"))
	for h in graph.M:opairs("Trm=Vrm") do
		setcts(graph.objs[h], subsetct)
	end
	-- all predicates must type according to the operator.
	for h in graph.M:opairs("Trp=Vrp") do
		local guard = graph.objs[h]
		local operator = guard.predicate.operator
		setcts(guard.lhs, predcts[operator] or error(string.format("invalid operator: '%s'", operator)))
	end
	-- all (non-guard) variables must now have a unique ctype.
	for h in graph.M:opairs("Trg=Vr") do
		local var = graph.objs[h]
		local ctype = selectctype(var.ctype)
		if not ctype then
			error(string.format("no possible ctype for variable '%s'", desc(var)))
		end
		var.ctype = ctype
		graph.M:set_size(h, ffi.sizeof(var.ctype))
	end
	-- resolve predicates now that we have typing info
	for h in graph.M:opairs("Trp=Vrp") do
		local guard = graph.objs[h]
		local predicate = guard.predicate
		graph.M:set_operator(predicate.handle,
			topredicate(predicate.operator, guard.lhs.ctype, graph_patchrhs(graph, predicate.rhs)))
	end
end

local function graph_errf(graph)
	local names = {}
	for _,o in pairs(graph.objs) do
		if o.idx and o.name then
			names[o.idx] = o.name
		end
	end
	return function(S)
		local err = ctypes.err(S.err)
		if err.obj and names[err.obj] then
			err.obj = names[err.obj]
		end
		error(tostring(err), 2)
	end
end

local function graph_impl(graph)
	graph.J[1] = ok
	-- prefill J first to make sure it doesn't become a hash table.
	for i=2, cdef.jtabsize(graph.M) do
		graph.J[i] = invalid
	end
	for h in graph.M:opairs("r") do
		local obj = graph.objs[h]
		if obj then
			local idx, jump = graph.M:query(obj.handle)
			if idx then
				obj.idx, obj.jump = idx, jump
				if jump then
					if obj.impl then
						-- TODO: if obj.lazy then ...
						local loader = obj.impl.loader
						if type(loader) == "string" then
							loader = require("fhk_lang_"..loader).load
							if not loader then
								error(string.format("module fhk_lang_%s doesn't export `load'", loader))
							end
						end
						graph.J[jump] = loader(graph.J, obj)
					else
						graph.J[jump] = hole(desc(obj))
					end
				end
			end
		end
	end
	graph.J[0] = graph_errf(graph)
end

local function graph_layout(graph)
	graph_typing(graph)
	checke(graph, graph.M:layout())
	graph_impl(graph)
end

---- graph building ----------------------------------------

local function graph_size(graph)
	return graph.M:size()
end

local function graph_build(graph, buf)
	return checkv(graph, graph.M:build(buf))
end

---- graph creation ----------------------------------------

local graph_mt = {
	__index = {
		getvar       = graph_getvar,
		addvar       = graph_addvar,
		setinverse   = graph_setinverse,
		setlhs       = graph_setlhs,
		setcheck     = graph_setcheck,
		addmodel     = graph_addmodel,
		getmodel     = graph_getmodel,
		setcost      = graph_setcost,
		addparam     = graph_addparam,
		addreturn    = graph_addreturn,
		addcheck     = graph_addcheck,
		addrcheck    = graph_addrcheck,
		addpredicate = graph_addpredicate,
		setpredicate = graph_setpredicate,
		dump         = graph_dump,
		setname      = graph_setname,
		read         = graph_read,
		analyze      = graph_analyze,
		mark         = graph_mark,
		layout       = graph_layout,
		size         = graph_size,
		build        = graph_build
	}
}

local ltab_mt = {
	__index = function(self, label)
		for _,f in ipairs(self) do
			local v = f(label)
			if v then
				self[label] = v
				return v
			end
		end
	end
}

local function graph(...)
	local M, err = ctypes.mut()
	if not M then error(tostring(err)) end
	ctypes.gc(M)
	local global = { handle=ctypes.mref_global, mode="s" }
	global.group = global
	-- ident explicitly doesn't have a group, since defining a group for ident
	-- doesn't make sense. better let it crash than do something unexpected if the
	-- group is accessed.
	local ident = { handle=ctypes.mref_ident, mode="s" }
	local graph = setmetatable({
		M      = M,  -- mut graph
		J      = {}, -- jump table
		objs   = {}, -- lookup: handle -> object
		lookup = {}, -- lookup: key    -> object
		virt   = {}, -- virtual variables
		global = global,
		ident  = ident,
		label  = setmetatable({}, ltab_mt), -- intrinsic check labels
	}, graph_mt)
	graph.objs[global.handle] = global
	graph.objs[ident.handle] = ident
	graph_setname(graph, global, "global#global")
	graph_setname(graph, ident, "<ident>")
	if #{...} > 0 then
		graph_read(graph, ...)
	end
	return graph
end

--------------------------------------------------------------------------------

return {
	xsplitname   = xsplitname,
	splitname    = splitname,
	desc         = desc,
	setcts       = setcts,
	getmode      = getmode,
	overridemode = overridemode,
	code         = code,
	funcname     = funcname,
	params       = params,
	returns      = returns,
	check        = check,
	cost         = cost,
	ctype        = ctype,
	inverse      = inverse,
	builtins     = builtins,
	virtual      = virtual,
	newimpl      = newimpl,
	impl         = impl,
	int          = ctint,
	fp           = ctfp,
	graph        = graph
}
