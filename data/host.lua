local ffi = require "ffi"
local buffer = require "string.buffer"
require "table.clear"
require "table.new"
local tensor, API, OP_NAMEPTR, OP_NAMEOFS, OP_FDESC, OP_FOFS, OP_NUM = ...
local API = ffi.cast("fhk_Api *", API)

---- String buffer management --------------------------------------------------

local function getstrbuf(graph)
	return ffi.string(API.fhk_buf(graph.G))
end

local function getstr(graph, str)
	API.fhk_getstr(graph.G, str)
	return getstrbuf(graph)
end

---- Object management ---------------------------------------------------------

-- ORDER FIELDTYPE
local FT_SPEC = 0
local FT_LIT  = 1
local FT_REF  = 2
local FT_NAME = 3
local FT_VLIT = 4
local FT_VREF = 5

-- ORDER PRI
local PRI_F64 = 0
local PRI_F32 = 1
local PRI_I64 = 2
local PRI_I32 = 3
local PRI_I16 = 4
local PRI_I8  = 5
local PRI_U64 = 6
local PRI_U32 = 7
local PRI_U16 = 8
local PRI_U8  = 9
local PRI_B1  = 10
local PRI_PTR = 11
local PRI_STR = 12
local PRI_CT = {
	[PRI_F64] = ffi.typeof("double"),
	[PRI_F32] = ffi.typeof("float"),
	[PRI_I64] = ffi.typeof("int64_t"),
	[PRI_I32] = ffi.typeof("int32_t"),
	[PRI_I16] = ffi.typeof("int16_t"),
	[PRI_I8]  = ffi.typeof("int8_t"),
	[PRI_U64] = ffi.typeof("uint64_t"),
	[PRI_U32] = ffi.typeof("uint32_t"),
	[PRI_U16] = ffi.typeof("uint16_t"),
	[PRI_U8]  = ffi.typeof("uint8_t"),
	[PRI_B1]  = ffi.typeof("bool"),
	[PRI_PTR] = ffi.typeof("void *"),
	[PRI_STR] = nil, -- TODO: const char *? should these be null terminated?
}

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

local function isseq(x)
	return type(x) == "table" and getmetatable(x).seq
end

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

local function objects_next(_, obj)
	return obj.next
end

-- note: skips NIL
local function graph_objects(graph)
	return objects_next, nil, graph.objs[0]
end

---- Parsing -------------------------------------------------------------------

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

-- must match host_Lua.rs
local PARSE_DEF = 0
local PARSE_EXPR = 1
local PARSE_VREF = 2
local PARSE_TEMPLATE = 3

local function checkparse(graph, what, src, ...)
	local res
	local args = {...}
	if #args > 0 or isseq(src) then
		if isseq(src) then
			src = src.i
		elseif type(src) == "string" then
			src = checkparse(graph, PARSE_TEMPLATE, src)
		else
			error("input must be a string or a template")
		end
		for i,a in ipairs(args) do
			if type(a) == "string" then
				args[i] = checkparse(graph, PARSE_TEMPLATE, a)
			elseif isseq(a) then
				args[i] = a.i
			elseif isobj(a) then
				args[i] = a.name.i
			else
				error("template argument must be a string or template")
			end
		end
		local cap, n = setbuf(graph, args)
		res = API.fhk_tparse(graph.G, src, cap, n, what)
	else
		res = API.fhk_parse(graph.G, src, #src, what)
	end
	return assert(checkres(graph, res))
end

local function graph_seq(graph, src, ...)
	if isseq(src) and select("#", ...) == 0 and not arg1 then return src end
	return setmetatable({i=checkparse(graph, PARSE_TEMPLATE, src, ...)}, graph.seq_mt)
end

local function defcreate(create)
	if create == nil then return true else return create end
end

local function graph_tab(graph, tab, create)
	if isobj(tab) then return tab end
	tab = API.fhk_gettab(graph.G, graph_seq(graph, tab).i, defcreate(create))
	if tab >= 0 then return graph.objs[tab] end
end

local function graph_define(graph, src, ...)
	checkparse(graph, PARSE_DEF, src, ...)
end

local function graph_var(graph, tab, name, create)
	tab = graph_tab(graph, tab, create)
	if not tab then return end
	local var = API.fhk_getvar(graph.G, graph_seq(graph, name).i, tab.i, defcreate(create))
	if var >= 0 then return graph.objs[var] end
end

local function graph_expr(graph, tab, src, ...)
	if isobj(src) then return src end
	API.fhk_settab(graph.G, graph_tab(graph, tab, true).i)
	return graph.objs[checkparse(graph, PARSE_EXPR, src, ...)]
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

---- Queries -------------------------------------------------------------------

local function query_add(query, expr)
	query.vnum = query.vnum+1
	query.values[query.vnum] = graph_expr(query.graph, query.tab, expr)
	return string.format("v%d", query.vnum)
end

local query_mt = {
	add = query_add
}
query_mt.__index = query_mt

local function graph_newquery(graph, tab, ...)
	local query = setmetatable({
		graph  = graph,
		tab    = graph_tab(graph, tab),
		values = {},
		vnum   = 0
	}, query_mt)
	table.insert(graph.queries, query)
	for _,v in ipairs({...}) do
		query_add(query, v)
	end
	return query
end

local function ann2ct(obj)
	if obj.ann then
		obj = obj.ann
	end
	if obj.op == "TPRI" then
		return PRI_CT[obj.ty]
	elseif obj.op == "TTEN" then
		return tensor.ctypeof(ann2ct(obj.elem), obj.dim)
	else
		error("bad type annotation")
	end
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

local function queryctype(query)
	local buf = buffer.new()
	buf:put("struct {\n")
	local args = {}
	for i,v in ipairs(query.obj.value) do
		buf:putf("$ v%d;\n", i)
		args[i] = ann2ct(v)
	end
	buf:put("}")
	return ffi.metatype(
		ffi.typeof(tostring(buf), unpack(args)),
		{
			__index = {
				unpack = queryunpack(query.vnum)
			}
		}
	)
end

local function queryfunc(ctype, mcode)
	-- TODO:
	-- * index parameter
	-- * proper error handling
	return load(string.format([[
		local ctype, fhk_vmcall = ...
		return function(instance, res)
			local ret = res or ctype()
			local r = fhk_vmcall(instance, ret, %s)
			assert(r == 0)
			return ret
		end
	]], ffi.cast("uintptr_t", mcode)))(ctype, API.fhk_vmcall)
end

local function compilequery(query, image)
	local ct = queryctype(query)
	local mcode = ffi.cast("const uint8_t *", image) + query.obj.mcode
	query.query = queryfunc(ct, mcode)
end

---- Resets --------------------------------------------------------------------

local function reset_add(reset, obj)
	if not isobj(obj) then
		obj = reset.graph.objs[checkparse(reset.graph, PARSE_VREF, obj)]
	end
	assert(obj.op == "VAR" or obj.op == "MOD", "only variables or models can be reset")
	table.insert(reset.objs, obj)
end

local reset_mt = {
	add = reset_add
}
reset_mt.__index = reset_mt

local function graph_newreset(graph, ...)
	local reset = setmetatable({
		graph = graph,
		objs  = {}
	}, reset_mt)
	table.insert(graph.resets, reset)
	for _,e in ipairs({...}) do
		reset_add(reset, e)
	end
	return reset
end

local function computemask(reset)
	if reset.obj.mhi == 0 then
		reset.mask = reset.obj.mlo
	else
		reset.mask = bit.bor(0ull+reset.obj.mlo, bit.lshift(0ull+reset.obj.mhi, 32))
	end
end

---- Instances -----------------------------------------------------------------

local function image_newinstance(image, alloc, udata, prev, mask)
	return API.fhk_newinstance(image, alloc, udata or nil, prev or nil, mask or -1ull)
end

local image_mt = {
	newinstance = image_newinstance
}
image_mt.__index = image_mt

ffi.metatype("fhk_Image", image_mt)

---- Compilation ---------------------------------------------------------------

local function graph_compile(graph)
	for _,query in ipairs(graph.queries) do
		query.obj = graph.objs[API.fhk_newquery(graph.G, query.tab.i, setbufo(graph, query.values))]
	end
	for _,reset in ipairs(graph.resets) do
		reset.obj = graph.objs[API.fhk_newreset(graph.G, setbufo(graph, reset.objs))]
	end
	local image = ffi.new("fhk_Image *[1]");
	assert(checkres(graph, API.fhk_compile(graph.G, image)))
	local ptr = image[0]
	local base = API.fhk_mcode(ptr)
	for _,query in ipairs(graph.queries) do
		compilequery(query, base)
	end
	for _,reset in ipairs(graph.resets) do
		computemask(reset)
	end
	return ffi.gc(ptr, API.fhk_destroyimage)
end

--------------------------------------------------------------------------------

local graph_mt = {
	objects  = graph_objects,
	seq      = graph_seq,
	define   = graph_define,
	var      = graph_var,
	expr     = graph_expr,
	newquery = graph_newquery,
	newreset = graph_newreset,
	dump     = graph_dump,
	compile  = graph_compile
}
graph_mt.__index = graph_mt

local function newgraph()
	local graph = setmetatable({
		G       = ffi.gc(API.fhk_newgraph(), API.fhk_destroygraph),
		buf     = ffi.new("int32_t[?]", 8),
		bufsz   = 8,
		num     = 0,
		queries = {},
		resets  = {},
	}, graph_mt)
	graph.obj_mt = makeobjmts(graph)
	graph.objs   = makeobjtab(graph)
	graph.seq_mt = makeseqmt(graph)
	return graph
end

return {
	newgraph = newgraph,
	refs     = obj_refs
}
