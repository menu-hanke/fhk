local ffi = require "ffi"
local buffer = require "string.buffer"
require "table.clear"
require "table.new"
local tensor, API, OP_NAMEPTR, OP_NAMEOFS, OP_FDESC, OP_FOFS, OP_NUM = ...
local API = ffi.cast("fhk_Api *", API)
local NODE_NIL = 0

local function getstrbuf(graph)
	return ffi.string(API.fhk_buf(graph.G))
end

local function getstr(graph, str)
	API.fhk_getstr(graph.G, str)
	return getstrbuf(graph)
end

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
	return getmetatable(obj).proto
end

local function isobj(x)
	return type(x) == "table" and getobjproto(x) ~= nil
end

local function isseq(x)
	return type(x) == "table" and getmetatable(x).seq
end

local function isvalidobj(graph, idx)
	if idx < graph.num then
		return true
	end
	graph.num = API.fhk_objnum(graph.G)
	return idx < graph.num
end

local function getobjptr(obj)
	return API.fhk_objs(getgraph(obj).G) + obj.idx
end

local fhk_Obj = ffi.typeof [[
	union {
		uint32_t raw;
		struct {
			uint8_t n;
			uint8_t op;
			uint8_t mark;
			uint8_t data;
		} obj;
	}
]]

local function raw2obj(raw)
	return fhk_Obj(raw).obj
end

local function fget_spec(obj)
	return raw2obj(getobjptr(obj)[0]).data
end

local function fget_lit(obj, i)
	return getobjptr(obj)[i]
end

local function fget_name(obj, i)
	return getstr(getgraph(obj), fget_lit(obj, i))
end

local function fget_ref(obj, i)
	return getgraph(obj).objs[fget_lit(obj, i)]
end

local function fget_vlit(obj, i)
	local ptr = getobjptr(obj)
	local n = raw2obj(ptr[0]).n - i
	local values = table.new(n, 0)
	for j=1, n do
		values[j] = ptr[i+j-1]
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

local function makeproto(fields)
	local proto = table.new(0, #fields)
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
		OPDEF[i] = {
			name   = ffi.string(OP_NAMEPTR+OP_NAMEOFS[i], OP_NAMEOFS[i+1]-OP_NAMEOFS[i]),
			fields = fields,
			proto  = makeproto(fields)
		}
	end
end

local function objtypeof(x)
	return OPDEF[getmetatable(x).opno].name
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
		proto   = OPDEF[opno].proto,
		opno    = opno,
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

local function objtab__index(self, idx)
	local graph = getgraph(self)
	if not isvalidobj(graph, idx) then
		return
	end
	local op = raw2obj(API.fhk_objs(graph.G)[idx]).op
	local obj = setmetatable({idx=idx}, graph.obj_mt[op])
	rawset(self, idx, obj)
	return obj
end

local function makeobjtab(graph)
	return setmetatable({}, {
		graph   = graph,
		__index = objtab__index
	})
end

local function seq__tostring(seq)
	return getstr(getgraph(seq), seq.idx)
end

local function makeseqmt(graph)
	return {
		graph      = graph,
		seq        = true,
		__tostring = seq__tostring
	}
end

local function checkbuf(graph, n)
	local bufsz = graph.bufsz
	if n > bufsz then
		repeat bufsz = 2*bufsz until n <= bufsz
		graph.buf = ffi.new("int32_t[?]", bufsz)
		graph.bufsz = bufsz
	end
end

local function setbuf(graph, values)
	checkbuf(graph, #values)
	for i=1, #values do
		graph.buf[i-1] = values[i]
	end
	return graph.buf, #values
end

local function setbufo(graph, objs)
	checkbuf(graph, #objs)
	for i=1, #objs do
		graph.buf[i-1] = objs[i].idx
	end
	return graph.buf, #objs
end

local function checkres(graph, x)
	if x == -1 then
		return nil, getstrbuf(graph)
	else
		return x
	end
end

local function defcreate(create)
	if create == nil then return true else return create end
end

local function gettemplate(graph, src)
	if isseq(src) then return src end
	if isobj(src) then
		error("TODO: return ObjRef name")
	end
	return setmetatable(
		{idx=assert(checkres(graph, API.fhk_gettemplate(graph.G, src, #src)))},
		graph.seq_mt
	)
end

-- local function substitute(graph, template, arg1, ...)
-- 	template = gettemplate(graph, template)
-- 	if arg1 == nil then return template end
-- 	local args = {}
-- 	for i,a in ipairs({arg1, ...}) do
-- 		args[i] = untagseq(gettemplate(graph, a))
-- 	end
-- 	return tagseq(assert(checkres(graph,
-- 		API.fhk_substitute(graph.G, template, setbuf(graph, args)))))
-- end

local function gettab(graph, tab, create)
	if isobj(tab) then return tab end
	tab = API.fhk_gettab(graph.G, gettemplate(graph, tab).idx, defcreate(create))
	if tab >= 0 then return graph.objs[tab] end
end

-- local function getvar(graph, tab, var, create)
-- 	if isobj(var) then return var end
-- 	create = defcreate(create)
-- 	tab = gettab(graph, tab, create)
-- 	if not tab then return end
-- 	var = API.fhk_getvar(graph.G, tab, untagseq(gettemplate(graph, var)), create)
-- 	if var >= 0 then return var end
-- end

-- local function fhk_get(graph, name, op, create)
-- 	return API.fhk_get(graph.G, name, OP_ID[op], create or false)
-- end

-- local function fhk_new(graph, op, args)
-- 	return API.fhk_new(graph.G, OP_ID[op], setbuf(graph, args))
-- end

-- local function fhk_args(graph, node)
-- 	-- TODO
-- end

local function query_add(query, expr)
	table.insert(
		query.values,
		query.graph.objs[assert(checkres(graph,
			API.fhk_parse(query.graph.G, query.tab.idx, expr, #expr)))]
	)
end

local query_mt = {
	add = query_add
}
query_mt.__index = query_mt

local function graph_newquery(graph, tab)
	local query = setmetatable({
		graph  = graph,
		tab    = gettab(graph, tab),
		values = {}
	}, query_mt)
	table.insert(graph.queries, query)
	return query
end

local reset_mt = {

}
reset_mt.__index = reset_mt

local function graph_newreset(graph)
	local reset = setmetatable({
		graph = graph,
		nodes = {}
	}, reset_mt)
	table.insert(graph.resets, reset)
	return reset
end

local function image_newinstance(image, alloc, udata, prev, mask)
	return API.fhk_newinstance(image.ptr, alloc, udata or nil, prev or nil, mask or 1)
end

local image_mt = {
	newinstance = image_newinstance
}
image_mt.__index = image_mt

local function graph_define(graph, src)
	assert(checkres(graph, API.fhk_define(graph.G, src, #src)))
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

local function ann2ct(obj)
	if obj.ann then
		obj = obj.ann
	end
	local aty = objtypeof(obj)
	if aty == "TPRI" then
		return PRI_CT[obj.ty]
	elseif aty == "TTEN" then
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
				unpack = queryunpack(#query.obj.value)
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

local function graph_compile(graph)
	for _,query in ipairs(graph.queries) do
		query.obj = graph.objs[API.fhk_newquery(graph.G, query.tab.idx, setbufo(graph, query.values))]
	end
	local image = ffi.new("fhk_Image *[1]");
	assert(checkres(graph, API.fhk_compile(graph.G, image)))
	local ptr = image[0]
	local base = API.fhk_mcode(ptr)
	for _,query in ipairs(graph.queries) do
		compilequery(query, base)
	end
	setmetatable(graph, image_mt)
	table.clear(graph)
	graph.ptr = ptr
	return graph
end

local graph_mt = {
	newquery = graph_newquery,
	newreset = graph_newreset,
	define   = graph_define,
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
	newgraph = newgraph
}
