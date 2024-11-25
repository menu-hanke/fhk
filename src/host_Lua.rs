//! Lua host support.

use core::ffi::{c_char, c_int, c_void};
use core::pin::Pin;

use alloc::boxed::Box;

use crate::bytestring::ByteString;
use crate::compile::{Ccx, Seq};
use crate::data::{HOST_LUA, TENSOR_LUA};
use crate::dump::dump_objs;
use crate::image::{Image, Instance};
use crate::intern::InternRef;
use crate::mem::applyreset;
use crate::obj::{LookupEntry, Obj, ObjRef, ObjType, Operator, EXPR, QUERY, TAB};
use crate::parse::{parse_def, parse_expr, parse_template};
use crate::parser::{parse, stringify, Parser, SequenceType};

use crate::image::fhk_vmcall_native as fhk_vmcall;

type lua_State = c_void;

extern "C-unwind" {
    fn luaL_loadbuffer(L: *mut lua_State, buff: *const u8, sz: usize, name: *const c_char) -> c_int;
    fn lua_call(L: *mut lua_State, nargs: c_int, nresults: c_int);
    fn lua_pushlightuserdata(L: *mut lua_State, p: *mut c_void);
    fn lua_pushinteger(L: *mut lua_State, n: isize);
}

type fhk_Graph = Ccx<Parser>;
type fhk_Image = Image;
type fhk_Instance = Instance;
type fhk_ObjRef<T=Obj> = ObjRef<T>;
type fhk_SeqRef = InternRef<Seq>;
type fhk_Operator = Operator;
type fhk_Result = i32;
type fhk_Alloc = unsafe extern "C" fn(*mut c_void, usize, usize) -> *mut u8;

#[derive(Default)]
pub struct HostCtx {
    pub buf: ByteString
}

pub struct HostInst {
    alloc: fhk_Alloc,
    udata: *mut c_void
}

impl HostInst {

    pub fn alloc(&mut self, size: usize, align: usize) -> *mut u8 {
        unsafe { (self.alloc)(self.udata, size, align) }
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
    drop(Box::from_raw(G))
}

unsafe extern "C" fn fhk_destroyimage(image: *mut fhk_Image) {
    drop(Box::from_raw(image))
}

extern "C" fn fhk_buf(G: &mut fhk_Graph) -> *const c_char {
    G.host.buf.null_terminate();
    G.host.buf.as_ptr() as _
}

extern "C" fn fhk_objs(G: &mut fhk_Graph) -> *mut u32 {
    G.objs.as_mut_ptr()
}

extern "C" fn fhk_objnum(G: &fhk_Graph) -> ObjRef {
    G.objs.end()
}

unsafe extern "C" fn fhk_gettemplate(
    G: &mut fhk_Graph,
    src: *const c_char,
    len: usize
) -> fhk_Result {
    match parse(G, core::slice::from_raw_parts(src as _, len), |pcx| parse_template(pcx)) {
        Err(_) => -1,
        Ok(seq) => zerocopy::transmute!(seq)
    }
}

extern "C" fn fhk_substitute(
    G: &mut fhk_Graph,
    template: fhk_SeqRef,
    subs: *const fhk_SeqRef,
    num: usize
) -> fhk_Result {
    todo!()
}

fn getobj<T, F>(entry: LookupEntry<'_, T, F>, create: bool) -> fhk_Result
    where T: ?Sized + ObjType, F: FnOnce() -> ObjRef<T>
{
    match (entry, create) {
        (LookupEntry::Occupied(idx), _) => zerocopy::transmute!(idx),
        (LookupEntry::Vacant(e), true)  => zerocopy::transmute!(e.create()),
        (LookupEntry::Vacant(_), false) => -2,
    }
}

extern "C" fn fhk_gettab(G: &mut fhk_Graph, name: fhk_SeqRef, create: bool) -> fhk_Result {
    getobj(G.objs.tab(name), create)
}

extern "C" fn fhk_getvar(
    G: &mut fhk_Graph,
    tab: fhk_ObjRef<TAB>,
    name: fhk_SeqRef,
    create: bool
) -> fhk_Result {
    getobj(G.objs.var(tab, name), create)
}

extern "C" fn fhk_getstr(G: &mut fhk_Graph, string: fhk_SeqRef) {
    G.host.buf.clear();
    stringify(
        &mut G.host.buf,
        &G.constants,
        G.sequences.get_slice(string.cast()),
        SequenceType::Pattern
    );
}

// extern "C" fn fhk_new(
//     G: &mut fhk_Graph,
//     op: fhk_Operator,
//     args: *mut fhk_ObjRef,
//     narg: usize
// ) -> fhk_ObjRef {
//     // new constant etc?
//     todo!()
// }

unsafe extern "C" fn fhk_parse(
    G: &mut fhk_Graph,
    tab: fhk_ObjRef<TAB>,
    src: *const c_char,
    len: usize
) -> fhk_Result {
    G.data.tab = tab;
    match parse(G, core::slice::from_raw_parts(src as _, len), parse_expr) {
        Err(_) => -1,
        Ok(idx) => zerocopy::transmute!(idx)
    }
}

unsafe extern "C" fn fhk_newquery(
    G: &mut fhk_Graph,
    tab: fhk_ObjRef<TAB>,
    values: *const fhk_ObjRef<EXPR>,
    num: usize
) -> fhk_ObjRef<QUERY> {
    G.objs.push(&QUERY::new(tab, 0, core::slice::from_raw_parts(values, num))).cast()
}

// extern "C" fn fhk_args(G: &mut fhk_Graph, node: fhk_ObjRef, ptr: *mut *mut fhk_ObjRef) -> fhk_Result {
//     // put ref in ptr, return size
//     todo!()
// }

unsafe extern "C" fn fhk_define(G: &mut fhk_Graph, src: *const c_char, len: usize) -> fhk_Result {
    match parse(G, core::slice::from_raw_parts(src as _, len), parse_def) {
        Ok(_) => 0,
        Err(_) => -1
    }
}

extern "C" fn fhk_dumpobjs(G: &mut fhk_Graph) {
    G.host.buf.clear();
    dump_objs(&mut G.host.buf, &G.constants, &G.sequences, &G.objs, ObjRef::NIL);
}

unsafe extern "C" fn fhk_compile(G: &mut fhk_Graph, image: *mut *mut fhk_Image) -> fhk_Result {
    let result = G.begin().unwrap().ccx.compile();
    match result {
        Ok(()) => {
            *image = Box::leak(Box::new(G.image.take().unwrap()));
            0
        },
        Err(()) => -1
    }
}

extern "C" fn fhk_mcode(image: &fhk_Image) -> *const u8 {
    image.mem.base()
}

unsafe extern "C" fn fhk_newinstance(
    image: &fhk_Image,
    alloc: fhk_Alloc,
    udata: *mut c_void,
    prev: *const fhk_Instance,
    reset: u64
) -> Pin<&mut fhk_Instance> {
    let mem = alloc(udata, image.size as _, align_of::<Instance>());
    if !prev.is_null() {
        // copy?
        todo!()
    }
    applyreset(mem, &image.breakpoints, reset);
    let mem = mem as *mut Instance;
    (*mem).host = HostInst { alloc, udata };
    Pin::new_unchecked(&mut *mem)
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
"require('ffi').cdef [[
typedef struct fhk_Graph fhk_Graph;
typedef struct fhk_Image fhk_Image;
typedef struct fhk_Instance fhk_Instance;
typedef void *(fhk_Alloc)(void *, size_t, size_t);",
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
    void (*fhk_destroyimage)(fhk_Image *);
    char *(*fhk_buf)(fhk_Graph *);
    uint32_t *(*fhk_objs)(fhk_Graph *);
    uint32_t (*fhk_objnum)(fhk_Graph *);
    int32_t (*fhk_gettemplate)(fhk_Graph *, const char *, size_t);
    int32_t (*fhk_substitute)(fhk_Graph *, int32_t, int32_t *, size_t);
    int32_t (*fhk_gettab)(fhk_Graph *, int32_t, bool);
    int32_t (*fhk_getvar)(fhk_Graph *, int32_t, int32_t, bool);
    void (*fhk_getstr)(fhk_Graph *, uint32_t);
    int32_t (*fhk_parse)(fhk_Graph *, int32_t, const char *, size_t);
    int32_t (*fhk_newquery)(fhk_Graph *, int32_t, int32_t *, size_t);
    // int32_t (*fhk_args)(fhk_Graph *, int32_t, int32_t *, size_t);
    int32_t (*fhk_define)(fhk_Graph *, const char *, size_t);
    void (*fhk_dumpobjs)(fhk_Graph *);
    int32_t (*fhk_compile)(fhk_Graph *, fhk_Image **);
    void *(*fhk_mcode)(fhk_Image *);
    fhk_Instance *(*fhk_newinstance)(fhk_Image *, fhk_Alloc *, void *, fhk_Instance *, uint64_t);
    int32_t (*fhk_vmcall)(fhk_Instance *, void *, uintptr_t);
}

#[no_mangle]
unsafe extern "C-unwind" fn luaopen_fhk(L: *mut lua_State) -> c_int {
    luaL_loadbuffer(L, HOST_APIDEF.as_ptr(), HOST_APIDEF.len(), c"fhk:hostapi".as_ptr());
    lua_call(L, 0, 0);
    luaL_loadbuffer(L, HOST_LUA.as_ptr(), HOST_LUA.len(), c"fhk".as_ptr());
    luaL_loadbuffer(L, TENSOR_LUA.as_ptr(), TENSOR_LUA.len(), c"fhk:tensor".as_ptr());
    lua_call(L, 0, 1);
    lua_pushlightuserdata(L, HOST_API.as_ptr() as _);
    lua_pushlightuserdata(L, Operator::NAME.as_ptr() as _);
    lua_pushlightuserdata(L, Operator::NAME_OFS.as_ptr() as _);
    lua_pushlightuserdata(L, Operator::FIELDS.0.as_ptr() as _);
    lua_pushlightuserdata(L, Operator::FIELDS.1.as_ptr() as _);
    lua_pushinteger(L, Operator::NAME_OFS.len() as isize - 1);
    lua_call(L, 7, 1);
    1
}
