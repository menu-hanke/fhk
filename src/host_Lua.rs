//! Lua host support.

use core::ffi::{c_char, c_int, c_void};
use core::fmt::Write;
use core::u64;

use alloc::boxed::Box;

use crate::bump::Bump;
use crate::compile::Ccx;
use crate::data::{HOST_LUA, TENSOR_LUA};
use crate::dump::dump_objs;
use crate::image::{Image, Instance};
use crate::intern::Interned;
use crate::mem::{Param, ParamId, Query, Reset};
use crate::obj::{Obj, ObjRef, Operator, EXPR, QUERY, TAB, TUPLE};
use crate::optimize::parse_optflags;
use crate::parse::{parse_expand_tab, parse_expand_var, parse_template, parse_toplevel_def, parse_toplevel_expr, ExpandResult};
use crate::parser::{parse, pushtemplate, stringify, Parser, SequenceType};

use crate::image::fhk_vmcall_native as fhk_vmcall;
use crate::FHK_VERSION_STRING;

type lua_State = c_void;

#[cfg_attr(windows, link(name="lua51"))]
unsafe extern "C-unwind" {
    fn luaL_loadbuffer(L: *mut lua_State, buff: *const u8, sz: usize, name: *const c_char)
        -> c_int;
    fn lua_call(L: *mut lua_State, nargs: c_int, nresults: c_int);
    fn lua_pushlightuserdata(L: *mut lua_State, p: *mut c_void);
    fn lua_pushinteger(L: *mut lua_State, n: isize);
    fn lua_pushstring(L: *mut lua_State, s: *const c_char);
}

// all of the following are accessed by ffi:
type fhk_Graph = Ccx<Parser>;
type fhk_Image = Image;
type fhk_Instance = Instance;
type fhk_ObjRef<T=Obj> = ObjRef<T>;
type fhk_SeqRef = Interned<[u8]>;
type fhk_Query = Query;
type fhk_Param = Param;
type fhk_Reset = Reset;
type fhk_Result = i32;
type fhk_Alloc = unsafe extern "C" fn(*mut c_void, usize, usize) -> *mut u8;

#[derive(Default)]
pub struct HostCtx {
    buf: Bump,
}

pub struct HostInst {
    alloc: fhk_Alloc,
    udata: *mut c_void,
    err: *const c_char
}

impl HostCtx {

    #[cold]
    pub fn set_error(&mut self, error: core::fmt::Arguments) {
        self.buf.clear();
        self.buf.write_fmt(error).unwrap();
    }

    #[cold]
    pub fn set_error_bytes(&mut self, error: &[u8]) {
        self.buf.clear();
        self.buf.write(error);
    }

}

impl HostInst {

    pub fn alloc(&mut self, size: usize, align: usize) -> *mut u8 {
        unsafe { (self.alloc)(self.udata, size, align) }
    }

    #[cold]
    pub fn set_error(&mut self, err: &[u8]) {
        let ptr = self.alloc(err.len()+1, 1);
        let data: &mut [u8] = unsafe { core::slice::from_raw_parts_mut(ptr, err.len()+1) };
        data[..err.len()].copy_from_slice(err);
        data[err.len()] = 0;
        self.err = ptr as _;
    }

}

extern "C" fn fhk_newgraph() -> *mut fhk_Graph {
    let ccx = Box::leak(Box::new(Ccx::new(Default::default())));
    // begin<Parse>() can't fail so this ceremony here is unnecessary but oh well.
    // it's only a couple lines longer than unwrap().
    if let Ok(parse) = ccx.begin() { return parse.leak() };
    // this can not use fhk_destroygraph() because ccx does NOT have a valid parse context.
    // (this would matter if begin<Parse> could fail...)
    unsafe { drop(Box::from_raw(ccx)) };
    core::ptr::null_mut()
}

unsafe extern "C" fn fhk_destroygraph(G: *mut fhk_Graph) {
    // NOTE: G must have a valid parse context even if we are done or errored out from compile
    drop(unsafe { Box::from_raw(G) })
}

unsafe extern "C" fn fhk_destroyimage(image: *mut fhk_Image) {
    drop(unsafe { Box::from_raw(image) })
}

extern "C" fn fhk_buf(G: &mut fhk_Graph) -> *const c_char {
    G.host.buf.null_terminate();
    G.host.buf.as_slice().as_ptr() as _
}

extern "C" fn fhk_objs(G: &mut fhk_Graph) -> *mut u32 {
    G.objs.as_mut_ptr()
}

extern "C" fn fhk_objnum(G: &fhk_Graph) -> ObjRef {
    G.objs.end()
}

unsafe fn slice_from_raw_parts<'a,T>(src: *const T, num: usize) -> &'a [T] {
    unsafe {
        core::slice::from_raw_parts(
            match num { 0 => core::mem::transmute(align_of::<T>()), _ => src },
            num
        )
    }
}

#[derive(Clone, Copy)]
enum Source<'a> {
    String(&'a [u8]),
    Template(fhk_SeqRef, &'a [fhk_SeqRef])
}

// options here must match host.lua
const PARSE_DEF: c_int      = 0;
const PARSE_EXPR: c_int     = 1;
const PARSE_TEMPLATE: c_int = 2;
const PARSE_TAB: c_int      = 3;
const PARSE_VAR: c_int      = 4;
const PARSE_CREATE: c_int   = 0x8; // flag to OR with PARSE_TAB or PARSE_VAR
fn doparse(G: &mut fhk_Graph, tab: fhk_ObjRef<TAB>, source: Source, what: c_int) -> fhk_Result {
    parse(
        G,
        match source { Source::String(s) => s, Source::Template(..) => &[] },
        |pcx| {
            pcx.data.tab = tab;
            if let Source::Template(template, captures) = source {
                pushtemplate(pcx, template, captures)?;
            }
            match what&0x7 {
                PARSE_DEF => parse_toplevel_def(pcx).map(|_| 0),
                PARSE_EXPR => parse_toplevel_expr(pcx).map(|o| zerocopy::transmute!(o)),
                PARSE_TEMPLATE => parse_template(pcx).map(|o| zerocopy::transmute!(o)),
                PARSE_TAB => Ok(match parse_expand_tab(pcx)? {
                    ExpandResult::Defined(o) => zerocopy::transmute!(o),
                    ExpandResult::Undefined(n) if (what & PARSE_CREATE) != 0 =>
                        zerocopy::transmute!(pcx.objs.tab(n).get_or_create()),
                    ExpandResult::Undefined(_) => 0
                }),
                PARSE_VAR => Ok(match parse_expand_var(pcx)? {
                    ExpandResult::Defined(o) => zerocopy::transmute!(o),
                    ExpandResult::Undefined((t,v)) if (what & PARSE_CREATE) != 0 => {
                        let tab = pcx.objs.tab(t).get_or_create();
                        zerocopy::transmute!(pcx.objs.var(tab,v).get_or_create())
                    },
                    ExpandResult::Undefined(_) => 0
                }),
                _ => unreachable!()
            }
        }
    ).unwrap_or(-1)
}

unsafe extern "C" fn fhk_parse(
    G: &mut fhk_Graph,
    tab: fhk_ObjRef<TAB>,
    src: *const c_char,
    len: usize,
    what: c_int
) -> fhk_Result {
    doparse(G, tab, Source::String(unsafe { slice_from_raw_parts(src as _, len) }), what)
}

unsafe extern "C" fn fhk_tparse(
    G: &mut fhk_Graph,
    tab: fhk_ObjRef<TAB>,
    template: fhk_SeqRef,
    caps: *const fhk_SeqRef,
    num: usize,
    what: c_int
) -> fhk_Result {
    doparse(G, tab, Source::Template(template, unsafe { slice_from_raw_parts(caps, num) }), what)
}

extern "C" fn fhk_getstr(G: &mut fhk_Graph, string: fhk_SeqRef) {
    G.host.buf.clear();
    stringify(&mut G.host.buf, &G.intern, &G.intern[string], SequenceType::Pattern);
}

unsafe extern "C" fn fhk_newquery(
    G: &mut fhk_Graph,
    values: *const fhk_ObjRef<EXPR>,
    num: usize
) -> fhk_ObjRef<QUERY> {
    let value = G.objs.push_args::<TUPLE>(TUPLE::new(ObjRef::NIL),
        unsafe { slice_from_raw_parts(values, num) });
    G.objs.push(QUERY::new(value))
}

extern "C" fn fhk_dumpobjs(G: &mut fhk_Graph) {
    G.host.buf.clear();
    dump_objs(&mut G.host.buf, &G.intern, &G.objs, ObjRef::NIL);
}

unsafe extern "C" fn fhk_optimize(G: &mut fhk_Graph, flags: *const c_char, len: usize) {
    G.flags = parse_optflags(unsafe { slice_from_raw_parts(flags as _, len) })
}

#[repr(C)]
struct fhk_CompileResult {
    image: *mut fhk_Image,
    mcode: *const u8,
    queries: *const fhk_Query,
    query_params: *const ParamId,
    params: *const fhk_Param,
    resets: *const fhk_Reset
}

unsafe extern "C" fn fhk_compile(G: &mut fhk_Graph, out: &mut fhk_CompileResult) -> fhk_Result {
    let ccx = &mut G.begin().unwrap().ccx;
    ccx.host.buf.clear();
    let Ok(image) = ccx.compile() else { return -1 };
    out.mcode = image.mem.base();
    out.image = Box::leak(Box::new(image));
    out.queries = ccx.layout.queries.raw.as_ptr();
    out.query_params = ccx.layout.query_params.as_ptr();
    out.params = ccx.layout.params.raw.as_ptr();
    out.resets = ccx.layout.resets.raw.as_ptr();
    0
}

extern "C" fn fhk_vmerr(instance: &fhk_Instance) -> *const c_char {
    instance.host.err as _
}

unsafe extern "C" fn fhk_newinstance(
    image: &fhk_Image,
    alloc: Option<fhk_Alloc>,
    udata: *mut c_void,
    template: *const fhk_Instance,
    reset: u64
) -> *mut fhk_Instance {
    // TODO: only reset if this query depends on the reset mask (save mask for queries too)
    // TODO: instead of copy-then-zero, just do both copying and zeroing in a single loop
    unsafe {
        let (alloc, udata) = match alloc {
            Some(alloc) => (alloc, udata),
            None => ((*template).host.alloc,
                if udata.is_null() { (*template).host.udata } else { udata })
        };
        let inst = image.instantiate(template, reset, |size, align| alloc(udata, size, align));
        (*inst).host = HostInst { alloc, udata, err: core::ptr::null() };
        inst
    }
}

macro_rules! define_api {
    (
        @tab
        $(
            $ret:ident $(*)*
            (*$name:ident)
            ($($params:tt)*)
            ;
        )*
    ) => {
        const HOST_API: &[*const c_void] = &[ $($name as _),* ];
    };
    ($($t:tt)*) => {
        const HOST_APIDEF: &str = concat!(
            "require('ffi').cdef [[",
            // layouts of all fhk_* structs must match this
            "
typedef struct fhk_Graph fhk_Graph;

typedef union {
    uint32_t raw;
    struct { uint8_t n; uint8_t op; uint8_t mark; uint8_t data; } obj;
} fhk_Obj;

typedef void *(fhk_Alloc)(void *, size_t, size_t);

typedef struct {
    uint32_t check;
    uint32_t value;
    uint32_t size;
} fhk_Param;

typedef struct {
    uint32_t mcode;
    uint32_t params_end;
    uint32_t vmctx_start;
    uint32_t vmctx_end;
} fhk_Query;

typedef struct {
    uint64_t mask;
} fhk_Reset;

typedef struct {
    void *image;
    uintptr_t mcode;
    fhk_Query *queries;
    uint16_t *query_params;
    fhk_Param *params;
    fhk_Reset *resets;
} fhk_CompileResult;
",
            stringify! {
                typedef struct {
                    $($t)*
                } fhk_Api;
            },
            "]]"
        );
        define_api!(@tab $($t)*);
    };
}

define_api! {
    fhk_Graph *(*fhk_newgraph)();
    void (*fhk_destroygraph)(fhk_Graph *);
    void (*fhk_destroyimage)(void *);
    char *(*fhk_buf)(fhk_Graph *);
    fhk_Obj *(*fhk_objs)(fhk_Graph *);
    uint32_t (*fhk_objnum)(fhk_Graph *);
    int32_t (*fhk_parse)(fhk_Graph *, int32_t, const char *, size_t, int);
    int32_t (*fhk_tparse)(fhk_Graph *, int32_t, int32_t, int32_t *, size_t, int);
    void (*fhk_getstr)(fhk_Graph *, uint32_t);
    int32_t (*fhk_newquery)(fhk_Graph *, int32_t *, size_t);
    void (*fhk_dumpobjs)(fhk_Graph *);
    void (*fhk_optimize)(fhk_Graph *, const char *, size_t);
    int32_t (*fhk_compile)(fhk_Graph *, void *);
    uint8_t *(*fhk_newinstance)(void *, fhk_Alloc *, void *, uint8_t *, uint64_t);
    int32_t (*fhk_vmcall)(void *, uintptr_t, uint8_t *);
    char *(*fhk_vmerr)(uint8_t *);
}

#[unsafe(no_mangle)]
unsafe extern "C-unwind" fn luaopen_fhk(L: *mut lua_State) -> c_int {
    unsafe {
        luaL_loadbuffer(L, HOST_APIDEF.as_ptr(), HOST_APIDEF.len(), c"fhk:hostapi".as_ptr());
        lua_call(L, 0, 0);
        luaL_loadbuffer(L, HOST_LUA.as_ptr(), HOST_LUA.len(), c"fhk".as_ptr());
        lua_pushstring(L, FHK_VERSION_STRING.as_ptr() as _);
        luaL_loadbuffer(L, TENSOR_LUA.as_ptr(), TENSOR_LUA.len(), c"fhk:tensor".as_ptr());
        lua_call(L, 0, 1);
        lua_pushlightuserdata(L, HOST_API.as_ptr() as _);
        lua_pushlightuserdata(L, Operator::NAME.as_ptr() as _);
        lua_pushlightuserdata(L, Operator::NAME_OFS.as_ptr() as _);
        lua_pushlightuserdata(L, Operator::FIELDS.0.as_ptr() as _);
        lua_pushlightuserdata(L, Operator::FIELDS.1.as_ptr() as _);
        lua_pushinteger(L, Operator::NAME_OFS.len() as isize - 1);
        lua_call(L, 8, 1);
    }
    1
}
