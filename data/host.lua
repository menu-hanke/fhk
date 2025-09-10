local ffi = require "ffi"
local buffer = require "string.buffer"
require "table.clear"
require "table.new"
local version, tensor, API, OP_NAMEPTR, OP_NAMEOFS, OP_FDESC, OP_FOFS, OP_NUM = ...
local API = ffi.cast("fhk_Api *", API)
local assert, pairs, type = assert, pairs, type
local bor = bit.bor

---- String buffer management --------------------------------------------------

local function getstrbuf(graph)
	return ffi.string(API.fhk_buf(graph.G))
end

local function getstr(graph, str)
	API.fhk_getstr(graph.G, str)
	return getstrbuf(graph)
end

---- Parse API -----------------------------------------------------------------

local function checkbuf(graph, n)
	local bufsz = graph.bufsz
	if n > bufsz then
		repeat bufsz = 2*bufsz until n <= bufsz
		graph.buf = ffi.new("int32_t[?]", bufsz)
		graph.bufsz = bufsz
	end
end

local function setbuf(graph, xs)
	checkbuf(graph, #xs)
	for i,x in ipairs(xs) do
		graph.buf[i-1] = x
	end
	return graph.buf, #xs
end

local function setbufo(graph, os)
	local xs = table.new(#os, 0)
	for i,o in ipairs(os) do
		xs[i] = o.i
	end
	return setbuf(graph, xs)
end

local function checkres(graph, x)
	if x == -1 then
		return nil, getstrbuf(graph)
	else
		return x
	end
end

local function isseq(x)
	return type(x) == "table" and getmetatable(x).seq
end

local function getgraph(x)
	return getmetatable(x).graph
end

local function getobjproto(obj)
	local mt = getmetatable(obj)
	if not mt then return end
	local opdef = mt.opdef
	if not opdef then return end
	return opdef.proto
end

local function isobj(x)
	return type(x) == "table" and getobjproto(x) ~= nil
end

-- must match host_Lua.rs
local PARSE_DEF = 0
local PARSE_EXPR = 1
local PARSE_TEMPLATE = 2
local PARSE_TAB = 3
local PARSE_VAR = 4
local PARSE_CREATE = 8

local function toseqidx(graph, x)
	if type(x) == "string" then
		return graph.seq[x].i
	elseif type(x) == "number" then
		return x
	elseif isseq(x) then
		return x.i
	elseif isobj(x) then
		return x.name.i
	else
		error(string.format("argument is not a string: `%s'", x))
	end
end

local function checkparse(graph, tab, what, src, ...)
	local res
	local args = {...}
	if #args == 0 and (type(src) == "string" or type(src) == "cdata" or type(src) == "userdata") then
		res = API.fhk_parse(graph.G, tab, src, #src, what)
	else
		src = toseqidx(graph, src)
		for i,a in ipairs(args) do
			args[i] = toseqidx(graph, a)
		end
		local cap, n = setbuf(graph, args)
		res = API.fhk_tparse(graph.G, tab, src, cap, n, what)
	end
	return assert(checkres(graph, res))
end

local function parsetemplate(graph, src, ...)
	if isseq(src) and select("#", ...) == 0 then return src end
	return setmetatable({i=checkparse(graph, 0, PARSE_TEMPLATE, src, ...)}, graph.seq_mt)
end

local function graph_define(graph, src, ...)
	checkparse(graph, 0, PARSE_DEF, src, ...)
end

local function createflag(create)
	if create == false then
		return 0
	else
		return PARSE_CREATE
	end
end

local function graph_tab(graph, tab, create, ...)
	if isobj(tab) then return tab end
	tab = checkparse(graph, 0, PARSE_TAB+createflag(create), tab, ...)
	if tab > 0 then return graph.objs[tab] end
end

local function graph_var(graph, tab, name, create, ...)
	local tabi
	if tab == nil then
		tabi = 0
	else
		tab = graph_tab(graph, tab, create)
		if not tab then return end
		tabi = tab.i
	end
	local var = checkparse(graph, tabi, PARSE_VAR+createflag(create), name, ...)
	if var > 0 then return graph.objs[var] end
end

local function graph_expr(graph, tab, src, ...)
	if isobj(src) then return src end
	return graph.objs[checkparse(graph, graph_tab(graph, tab).i, PARSE_EXPR, src, ...)]
end

local function graph_dump(graph, flags)
	-- NOTE: this is really inefficient and does a bunch of unnecessary copies,
	-- but it's only for debugging anyway.
	local buf = buffer.new()
	flags = flags or "o"
	if flags:match("o") then
		API.fhk_dumpobjs(graph.G)
		buf:put(getstrbuf(graph))
	end
	return buf:get()
end

---- Settings ------------------------------------------------------------------

local function graph_optimize(graph, flags)
	API.fhk_optimize(graph.G, flags, #flags)
end

---- Object management ---------------------------------------------------------

-- ORDER FIELDTYPE
local FT_SPEC = 0
local FT_LIT  = 1
local FT_REF  = 2
local FT_NAME = 3
local FT_VLIT = 4
local FT_VREF = 5

local function isvalidobj(graph, i)
	if i < graph.num then
		return true
	end
	graph.num = API.fhk_objnum(graph.G)
	return i < graph.num
end

local function getobjptr(obj)
	return API.fhk_objs(getgraph(obj).G) + obj.i
end

local function fget_spec(obj)
	return getobjptr(obj).obj.data
end

local function fget_lit(obj, i)
	return getobjptr(obj)[i].raw
end

local function fget_name(obj, i)
	return setmetatable({i=fget_lit(obj, i)}, getgraph(obj).seq_mt)
end

local function fget_ref(obj, i)
	return getgraph(obj).objs[fget_lit(obj, i)]
end

local function fget_vlit(obj, i)
	local ptr = getobjptr(obj)
	local n = ptr.obj.n - i
	local values = table.new(n, 0)
	for j=1, n do
		values[j] = ptr[i+j-1].raw
	end
	return values
end

local function fget_vref(obj, i)
	local values = fget_vlit(obj, i)
	local objs = getgraph(obj).objs
	for j=1, #values do
		values[j] = objs[values[j]]
	end
	return values
end

local FTGETTER = {
	[FT_SPEC] = fget_spec,
	[FT_LIT]  = fget_lit,
	[FT_REF]  = fget_ref,
	[FT_NAME] = fget_name,
	[FT_VLIT] = fget_vlit,
	[FT_VREF] = fget_vref
}

local function obj_next(obj)
	return getgraph(obj).objs[obj.i + getobjptr(obj).obj.n]
end

local function makeproto(fields, name)
	local proto = table.new(0, #fields+1)
	proto.op = function() return name end
	proto.next = obj_next
	for _,f in ipairs(fields) do
		local idx = f.idx
		local get = FTGETTER[f.ft]
		proto[f.name] = function(obj) return get(obj, idx) end
	end
	return proto
end

local OPDEF = table.new(OP_NUM, 0)
do
	local OP_NAMEPTR = ffi.cast("const char *", OP_NAMEPTR)
	local OP_NAMEOFS = ffi.cast("uint16_t *", OP_NAMEOFS)
	local OP_FDESC = ffi.cast("uint8_t *", OP_FDESC)
	local OP_FOFS = ffi.cast("uint16_t *", OP_FOFS)
	for i=0, OP_NUM-1 do
		local fields = {}
		local ofs = OP_FOFS[i]
		local j = 0
		while ofs < OP_FOFS[i+1] do
			local ft = bit.band(OP_FDESC[ofs], 0x7)
			if ft ~= FT_SPEC then
				j = j+1
			end
			local len = bit.rshift(OP_FDESC[ofs], 3)
			table.insert(fields, {
				ft   = ft,
				idx  = j,
				name = ffi.string(OP_FDESC+ofs+1, len)
			})
			ofs = ofs + 1 + len
		end
		local name = ffi.string(OP_NAMEPTR+OP_NAMEOFS[i], OP_NAMEOFS[i+1]-OP_NAMEOFS[i])
		OPDEF[i] = {
			fields = fields,
			proto  = makeproto(fields, name)
		}
	end
end

local function obj__index(self, name)
	local get = getobjproto(self)[name]
	if get ~= nil then
		local value = get(self)
		rawset(self, name, value)
		return value
	end
end

local function makeobjmt(graph, opno)
	return {
		graph   = graph,
		opdef   = OPDEF[opno],
		__index = obj__index
	}
end

local function makeobjmts(graph)
	local obj_mt = table.new(OP_NUM, 0)
	for i=0, OP_NUM-1 do
		obj_mt[i] = makeobjmt(graph, i)
	end
	return obj_mt
end

local function objtab__index(self, i)
	local graph = getgraph(self)
	if not isvalidobj(graph, i) then
		return
	end
	local op = API.fhk_objs(graph.G)[i].obj.op
	local obj = setmetatable({i=i}, graph.obj_mt[op])
	rawset(self, i, obj)
	return obj
end

local function obj_refs(obj)
	local refs = {}
	for _,f in pairs(getmetatable(obj).opdef.fields) do
		if f.ft == FT_REF then
			table.insert(refs, fget_ref(obj, f.idx))
		elseif f.ft == FT_VREF then
			for _,v in ipairs(fget_vref(obj, f.idx)) do
				table.insert(refs, v)
			end
		end
	end
	return refs
end

local function makeobjtab(graph)
	return setmetatable({}, {
		graph   = graph,
		__index = objtab__index
	})
end

-- TODO: cache string value
local function seq__tostring(seq)
	return getstr(getgraph(seq), seq.i)
end

local function makeseqmt(graph)
	return {
		graph      = graph,
		seq        = true,
		__tostring = seq__tostring
	}
end

local function seqtab__index(self, seq)
	if type(seq) ~= "string" then
		-- TODO: int index like objs?
		error("TODO")
	end
	local s = parsetemplate(getgraph(self), seq)
	self[seq] = s
	return s
end

local function makeseqtab(graph)
	return setmetatable({}, {
		graph   = graph,
		__index = seqtab__index
	})
end

local function objects_next(_, obj)
	return obj.next
end

-- note: skips NIL
local function graph_objects(graph)
	return objects_next, nil, graph.objs[0]
end

---- Queries -------------------------------------------------------------------

local function graph_query(graph, ...)
	local exprs = {...}
	for i,v in ipairs(exprs) do
		exprs[i] = graph_expr(graph, "global", v)
	end
	local idx = #graph.queries+1
	graph.queries[idx] = graph.objs[API.fhk_newquery(graph.G, setbufo(graph, exprs))]
	return string.format("q%d", idx)
end

---- Instances -----------------------------------------------------------------

-- TODO: consider unrolling this when there are only few resets
local function image_mask(image, mask)
	local m = 0ULL
	local rmask = image.reset
	for f,v in pairs(mask) do
		if v == true then
			m = bor(m, rmask[f] or 0ull)
		end
	end
	return m
end

local fhk_newinstance = API.fhk_newinstance
local function image_instance(image, alloc, udata, template, mask)
	if mask then
		if type(mask) == "table" then
			mask = image_mask(image, mask)
		end
	else
		mask = -1ULL
	end
	return fhk_newinstance(image.ptr, alloc, udata, template, mask)
end

local function image_exec(image, query, params)
	-- TODO: shortcut function: create a temp allocator here and attach finalizer to result
	error("TODO")
end

local image_mt = {
	mask = image_mask,
	instance = image_instance,
	exec = image_exec
}
image_mt.__index = image_mt

---- Compilation ---------------------------------------------------------------

local function decodeslot(slot)
	return bit.rshift(slot, 3), bit.band(slot, 0x7)
end

local function ann2ct(obj)
	if obj.ann then
		obj = obj.ann
	end
	if obj.op == "TPRI" then
		return tensor.scalar_ctype(obj.ty)
	elseif obj.op == "TTEN" then
		return tensor.tensor_ctype(ann2ct(obj.elem), obj.dim)
	else
		error("bad type annotation")
	end
end

local function newparam(check, value, var)
	local cbyte, cbit = decodeslot(check)
	local vbyte = decodeslot(value)
	local ctype = ann2ct(var)
	local buf = buffer.new()
	buf:put("local ffi_cast, bor, ctptr = require('ffi').cast, bit.bor, ...\n")
	buf:put("return function(instance, params)\n")
	buf:putf("local value = params and params['%s']\n", var.name)
	buf:put("if value == nil then return end\n")
	buf:putf("instance[%d] = bor(instance[%d], %d)\n", cbyte, cbyte, bit.lshift(1, cbit))
	if ctype then
		if var.ann.op == "TPRI" then
			buf:putf("ffi_cast(ctptr, instance+%d)[0] = value\n", vbyte)
		else
			-- TODO: call utility function:
			-- * if c value -> set pointers
			-- * if lua value -> alloc from instance + copy
			error("TODO")
		end
	end
	buf:put("end")
	return {
		func = load(buf)(ctype and ffi.typeof("$*", ctype)),
		cbyte = cbyte
	}
end

local function queryunpack(n)
	local buf = buffer.new()
	buf:put("return function(x)\nreturn ")
	for i=1, n do
		if i > 1 then buf:put(",") end
		buf:putf("x.v%d", i)
	end
	buf:put("\nend")
	return load(buf)()
end

local fhk_vmcall = API.fhk_vmcall
local function vmcall(result, mcode, instance)
	local r = fhk_vmcall(result, mcode, instance)
	if r ~= 0 then
		error(ffi.string(API.fhk_vmerr(instance)), 2)
	end
	return result
end

local function query__call(query, ...)
	return query.exec(...)
end

local query_mt = { __call = query__call }

local function compilequery(mcode, ty, params, vmctx_start, vmctx_end)
	local buf = buffer.new()
	buf:put("struct {\n")
	local ctargs = {}
	for i,e in ipairs(ty.elems) do
		buf:putf("$ v%d;\n", i)
		ctargs[i] = ann2ct(e)
	end
	buf:put("}")
	local ctype = ffi.typeof(buf:get(), unpack(ctargs))
	ffi.metatype(ctype, {__index = { unpack = queryunpack(#ty.elems) }})
	buf:put("local ffi_fill, ctype, vmcall")
	local pf = {}
	local minofs, maxofs = math.huge, 0
	for i,p in ipairs(params) do
		buf:putf(", setparam%d", i)
		pf[i] = p.func
		minofs = math.min(minofs, p.cbyte)
		maxofs = math.max(maxofs, p.cbyte)
	end
	buf:put("= ...\nreturn function(instance, params, res)\n")
	if vmctx_end > vmctx_start then
		buf:putf("ffi_fill(instance+%d, %d)\n", vmctx_start, vmctx_end-vmctx_start)
	end
	for i=1, #params do
		buf:putf("setparam%d(instance, params)\n", i)
	end
	buf:put("if not res then res = ctype() end\n")
	buf:putf("return vmcall(res, %dull, instance)\n", mcode)
	buf:put("end\n")
	local exec = load(buf)(ffi.fill, ctype, vmcall, unpack(pf))
	return setmetatable({
		exec = exec,
		ctype = ctype,
	}, query_mt)
end

local function graph_compile(graph)
	local result = ffi.new("fhk_CompileResult")
	assert(checkres(graph, API.fhk_compile(graph.G, result)))
	local params, resets = {}, {}
	local nparam, nreset = 0, 1
	local tabs = {}
	for o in graph:objects() do
		if o.op == "TAB" then
			tabs[tostring(o.name)] = o
		elseif o.op == "VAR" then
			if o.tab == tabs.state then
				resets[tostring(o.name)] = result.resets[nreset].mask
				nreset = nreset+1
			elseif o.tab == tabs.query then
				local rp = result.params[nparam]
				params[nparam] = newparam(rp.check, rp.value, o)
				nparam = nparam+1
			end
		end
	end
	local image = setmetatable({}, image_mt)
	image.ptr = ffi.gc(result.image, API.fhk_destroyimage)
	image.reset = resets
	local params_start = 0
	for i,q in ipairs(graph.queries) do
		local rq = result.queries[i-1]
		local qparm = {}
		for j=params_start, rq.params_end-1 do
			table.insert(qparm, params[result.query_params[j]])
		end
		params_start = rq.params_end
		image[string.format("q%d", i)] = compilequery(result.mcode+rq.mcode, q.value.ann, qparm,
			rq.vmctx_start, rq.vmctx_end)
	end
	return image
end

--------------------------------------------------------------------------------

local graph_mt = {
	objects  = graph_objects,
	define   = graph_define,
	var      = graph_var,
	expr     = graph_expr,
	query    = graph_query,
	dump     = graph_dump,
	optimize = graph_optimize,
	compile  = graph_compile
}
graph_mt.__index = graph_mt

local function newgraph()
	local graph = setmetatable({
		G       = ffi.gc(API.fhk_newgraph(), API.fhk_destroygraph),
		buf     = ffi.new("int32_t[?]", 8),
		bufsz   = 8,
		num     = 0,
		queries = {}
	}, graph_mt)
	graph.obj_mt = makeobjmts(graph)
	graph.objs   = makeobjtab(graph)
	graph.seq_mt = makeseqmt(graph)
	graph.seq    = makeseqtab(graph)
	return graph
end

return {
	version  = version,
	newgraph = newgraph,
	refs     = obj_refs,
	istensor = tensor.istensor
}
