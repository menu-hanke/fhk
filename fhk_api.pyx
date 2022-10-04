# cython: language_level=3
import cython
from cpython.buffer cimport PyBUF_READ
from cpython.mem cimport PyMem_Malloc, PyMem_Free
from cpython.memoryview cimport PyMemoryView_FromMemory
from libc.stdint cimport intptr_t, int64_t, int16_t, uint16_t, uint8_t
from collections.abc import Iterable
from inspect import Signature, signature
from typing import Iterable as TypingIterable, get_args, get_origin

cdef extern from *:
    """
    #include <lua.h>
    #include <lualib.h>
    #include <lauxlib.h>

    #include <stddef.h>

    #define FHK_PYX_GRAPH      "!@fhk_pyx_graph"

    static int fhk_pyx_traceback(lua_State *L) {
        luaL_traceback(L, L, lua_tostring(L, 1), 1);
        return 1;
    }

    static void *fhk_pyx_newstate() {
        lua_State *L = luaL_newstate();
        if(!L) return NULL;
        luaL_openlibs(L);
        lua_getfield(L, LUA_GLOBALSINDEX, "require");
        lua_pushliteral(L, "fhk_pyx");
        lua_call(L, 1, 1);
        lua_getfield(L, -1, "graph");
        lua_setfield(L, LUA_REGISTRYINDEX, FHK_PYX_GRAPH);
        lua_pop(L, 1);
        // traceback handler left on stack for the rest of the lifetime of this lua state.
        lua_pushcfunction(L, fhk_pyx_traceback);
        return L;
    }

    static void fhk_pyx_loadmethod(lua_State *L, int ref, const char *name) {
        lua_rawgeti(L, LUA_REGISTRYINDEX, ref); /* obj */
        lua_getfield(L, -1, name);              /* obj, meth */
        lua_insert(L, -2);                      /* meth, obj */
    }

    #include "api.h"
    #include "sub.h"

    static void fhk_pyx_setrootM_group(fhk_solver *S, int idx) {
        fhk_setrootM(S, idx, grefmeta(S->G, ~(xidx)idx).group, 0);
    }

    static fhk_subset fhk_pyx_space(fhk_solver *S, xidx idx) {
        return *(fhk_subset *) srefV(S2ref(S), grefmeta(S->G, ~idx).group);
    }

    static PyObject *fhk_pyx_memV(fhk_solver *S, xidx idx) {
        // danger: we don't actually care about the size here, so just set something big.
        return PyMemoryView_FromMemory(srefV(S2ref(S), idx), 0x100000000, PyBUF_WRITE);
    }

    static size_t fhk_pyx_size(fhk_solver *S, xidx idx) {
        return grefmeta(S->G, ~idx).size;
    }

    static xinst subset_size(fhk_subset ss) {
        if(LIKELY(subset_isIE(ss))) return subsetIE_size(ss);
        fhk_pkref pk = subsetC_pk(ss);
        xinst size = 0;
        for(;;) {
            size += pkref_size(pk);
            if(!pkref_more(pk)) return size;
            pk = pkref_next(pk);
        }
    }

    // hack to make cython output __declspec(dllexport) on windows.
    #define FHK_API_fhk_pyx_setrootinfo            FHK_API fhk_pyx_setrootinfo
    #define FHK_API_fhk_pyx_setvalue_scatter_space FHK_API fhk_pyx_setvalue_scatter_space
    #define FHK_API_fhk_pyx_setvalue_scatter2      FHK_API fhk_pyx_setvalue_scatter2
    """

    int LUA_REGISTRYINDEX
    const char *FHK_PYX_GRAPH
    const char *FHK_PYX_TRACEBACK
    ctypedef struct lua_State
    void lua_pop(lua_State *, int)
    int lua_gettop(lua_State *)
    int lua_pcall(lua_State *, int, int, int)
    void lua_pushnil(lua_State *)
    void lua_pushstring(lua_State *, const char *)
    void lua_pushlightuserdata(lua_State *, void *)
    void lua_pushboolean(lua_State *, int)
    int64_t lua_tointeger(lua_State *, int)
    const char *lua_tostring(lua_State *, int)
    void lua_getfield(lua_State *, int, const char *)
    int luaL_ref(lua_State *, int)
    void luaL_unref(lua_State *, int, int)
    void lua_rawgeti(lua_State *, int, int)
    void lua_close(lua_State *)
    lua_State *fhk_pyx_newstate()
    int fhk_pyx_graph(lua_State *)
    void fhk_pyx_loadmethod(lua_State *, int, const char *)

    ctypedef int64_t fhk_subset
    ctypedef uint8_t *fhk_pkref
    fhk_subset SUBSET_EMPTY
    fhk_subset SUBSET_UNDEF
    int subset_isIE(fhk_subset)
    fhk_subset subsetI_new(int, int)
    int subsetI_first(fhk_subset)
    int subsetIE_size(fhk_subset)
    fhk_pkref subsetC_pk(fhk_subset)
    fhk_subset subsetC_new(fhk_pkref)
    int pkref_first(fhk_pkref)
    int pkref_size(fhk_pkref)
    int pkref_more(fhk_pkref)
    fhk_pkref pkref_next(fhk_pkref)
    fhk_pkref pkref_prev(fhk_pkref)
    void pkref_write(fhk_pkref, int, int)

    ctypedef struct fhk_graph

    ctypedef struct fhk_mem:
        intptr_t tail
    fhk_mem *fhk_create_mem()
    void fhk_destroy_mem(fhk_mem *)
    void fhk_reset_mem(fhk_mem *)

    ctypedef struct fhk_solver:
        fhk_mem *mem
    fhk_solver *fhk_create_solver(fhk_mem *, fhk_graph *)
    void fhk_setrootK(fhk_solver *, int, fhk_subset)
    void *fhk_getvalueD(fhk_solver *, int, fhk_subset)
    void *fhk_setvalueD(fhk_solver *, int, fhk_subset)
    void fhk_pyx_setrootM_group(fhk_solver *, int)
    fhk_subset fhk_pyx_space(fhk_solver *, int)
    object fhk_pyx_memV(fhk_solver *, int)
    int fhk_pyx_size(fhk_solver *, int)
    int subset_size(fhk_subset)
    void fhk_mem_commit_tail(fhk_mem *, intptr_t)

    const char *FHK_GITHASH

version = f"fhk-{FHK_GITHASH.decode('utf8')}"

class FhkError(Exception):
    pass

@cython.auto_pickle(False)
cdef class GCLua:
    cdef lua_State *L
    cdef int16_t tb

    def __cinit__(self):
        self.L = fhk_pyx_newstate()
        if self.L == NULL:
            raise FhkError("failed to create lua state")
        self.tb = lua_gettop(self.L)

    def __dealloc__(self):
        lua_close(self.L)

    cdef int pcall(self, int narg, int nret) except -1:
        cdef int r = lua_pcall(self.L, narg, nret, self.tb)
        if r != 0:
            self.raise_()

    def raise_(self):
        raise FhkError(lua_tostring(self.L, -1).decode("utf8"))

    cdef void pushoptstring(self, object s):
        if s is None:
            lua_pushnil(self.L)
        else:
            lua_pushstring(self.L, s.encode("utf8"))

@cython.auto_pickle(False)
cdef class GCGraph:
    cdef void *base
    cdef fhk_graph *G
    cdef GCLua lua
    cdef int16_t refj

    def __cinit__(self, lua, refj):
        self.lua = lua
        self.refj = refj

    def __dealloc__(self):
        if self.lua is not None:
            luaL_unref(self.lua.L, LUA_REGISTRYINDEX, self.refj)
        if self.base != NULL:
            # allocation is in fhk_pyx.lua - this must match.
            PyMem_Free(self.base)

@cython.auto_pickle(False)
cdef class Mem:
    cdef fhk_mem *mem

    def __cinit__(self):
        self.mem = fhk_create_mem()

    def __dealloc__(self):
        self.destroy()

    def __enter__(self):
        return self

    def __exit__(self, exc, val, tb):
        self.destroy()

    def reset(self):
        if self.mem == NULL:
            raise FhkError("memory is destroyed")
        fhk_reset_mem(self.mem)

    def destroy(self):
        if self.mem != NULL:
            fhk_destroy_mem(self.mem)
        self.mem = NULL

@cython.auto_pickle(False)
cdef class Solver:
    cdef GCGraph graph    # ref needed here to keep graph alive
    cdef Mem mem          # ref needed here to keep mem alive
    cdef fhk_solver *S

    def __init__(self, graph, mem=None):
        if mem is None:
            mem = Mem()
        self.graph = graph
        self.mem = mem
        if self.graph.G == NULL:
            raise FhkError("graph is null, did you forget to call prepare()?")
        self.S = fhk_create_solver(self.mem.mem, self.graph.G)

@cython.auto_pickle(False)
cdef class PyxRoot:
    cdef str attr
    cdef str fmt
    cdef object vec
    cdef object new
    cdef uint16_t idx

    def __cinit__(self, attr):
        self.attr = attr

cdef public void FHK_API_fhk_pyx_setrootinfo(void *r, void *fmt, int idx):
    (<PyxRoot>r).fmt = <str> fmt
    (<PyxRoot>r).idx = idx

cdef fhk_subset tosubset(fhk_solver *S, object o) except -2:
    if isinstance(o, int):
        return o
    cdef list inst = sorted(o)
    if len(inst) == 0:
        return SUBSET_EMPTY
    cdef int i = len(inst)-1
    cdef int j
    cdef int last = inst[i]
    cdef int first = last
    while True:
        if i == 0:
            return subsetI_new(first, last-first)
        i -= 1
        j = inst[i]
        if j < first-1:
            break
        first = j
    cdef fhk_mem *mem = S.mem
    cdef fhk_pkref pk = <fhk_pkref> mem.tail
    pk -= 3
    pk[0] = 0
    pk[1] = 0
    pk[2] = 0
    pk = pkref_prev(pk)
    while True:
        fhk_mem_commit_tail(mem, <intptr_t> pk)
        pkref_write(pk, first, last-first)
        pk = pkref_prev(pk)
        last = j
        first = last
        while True:
            if i == 0:
                fhk_mem_commit_tail(mem, <intptr_t> pk)
                pkref_write(pk, first, last-first)
                mem.tail = <intptr_t> pk
                return subsetC_new(pk)
            i -= 1
            j = inst[i]
            if j < first-1:
                break
            first = j

def interval0(a, b=None):
    if b is None:
        a, b = 0, a
    return subsetI_new(a, b)

def interval1(a, b=None):
    if b is None:
        a, b = 0, a
    if b == 0:
        return SUBSET_EMPTY
    b -= 1
    return subsetI_new(a, b)

@cython.auto_pickle(False)
cdef class QueryFn:
    cdef GCGraph graph
    cdef object result
    cdef tuple roots

    def __cinit__(self, graph, result, roots):
        self.graph = graph
        self.result = result
        self.roots = roots

    def __call__(self, state=None, *, solver=None, mem=None, subsets=None):
        if solver is None:
            if mem is None:
                mem = Mem()
            solver = Solver(self.graph, mem)
        cdef fhk_solver *S = (<Solver?>solver).S
        cdef list subv = [SUBSET_UNDEF] * len(self.roots)
        cdef fhk_subset st
        cdef PyxRoot r
        for i,r_ in enumerate(self.roots):
            r = <PyxRoot> r_
            ss = subsets and subsets.get(r.attr)
            if ss is None:
                fhk_pyx_setrootM_group(S, r.idx)
            else:
                st = tosubset(S, ss)
                subv[i] = st
                fhk_setrootK(S, r.idx, st)
        cdef lua_State *L = self.graph.lua.L
        lua_rawgeti(L, LUA_REGISTRYINDEX, self.graph.refj)
        lua_pushlightuserdata(L, S)
        lua_pushlightuserdata(L, <void*>state)
        self.graph.lua.pcall(2, 0)
        cdef void *vp
        cdef int size
        cdef object result = self.result()
        for i,r_ in enumerate(self.roots):
            r = <PyxRoot> r_
            st = subv[i]
            if st == SUBSET_UNDEF:
                st = fhk_pyx_space(S, r.idx)
            size = subset_size(st)
            value = PyMemoryView_FromMemory(
                <char*>fhk_getvalueD(S, r.idx, st),
                subset_size(st)*fhk_pyx_size(S, r.idx),
                PyBUF_READ
            ).cast(r.fmt)
            if r.vec:
                if r.vec != memoryview:
                    if r.new != None:
                        value = map(r.new, value)
                    value = r.vec(value)
            else:
                value = value[0]
                if r.new != None:
                    value = r.new(value)
            setattr(result, r.attr, value)
        return result

cdef class root:
    cdef str name

    def __init__(self, name):
        self.name = name

EMPTYSET = -1
# for whatever reason Iterable[int] doesn't work.
Subset = int|Iterable.__class_getitem__(int)
def issubsettype(t):
    return t == Subset or issubclass(t, (int, Iterable))

# blame python devs for this absolute mess that are the subtly incompatible `typing`, `types`,
# and `collections.abc` modules.
# zen of python and only one way to do things, yeah...
def isiterabletype(t):
    try:
        return issubclass(t, Iterable)
    except TypeError:
        pass
    try:
        return issubclass(t, TypingIterable)
    except TypeError:
        pass
    return False

@cython.auto_pickle(False)
cdef class Graph:
    cdef GCLua lua
    cdef GCGraph graph
    cdef int16_t ref

    def __init__(self, *files, lua=None):
        if lua is None:
            lua = GCLua()
        self.lua = lua
        lua_getfield(self.lua.L, LUA_REGISTRYINDEX, FHK_PYX_GRAPH)
        self.lua.pcall(0, 2)
        self.graph = GCGraph(self.lua, luaL_ref(self.lua.L, LUA_REGISTRYINDEX))
        self.ref = luaL_ref(self.lua.L, LUA_REGISTRYINDEX)
        self.read(*files)

    def __dealloc__(self):
        if self.lua is not None:
            luaL_unref(self.lua.L, LUA_REGISTRYINDEX, self.ref)

    def __enter__(self):
        return self

    def __exit__(self, cls, val, tb):
        self.prepare()

    def read(self, *files):
        for f in files:
            fhk_pyx_loadmethod(self.lua.L, self.ref, b"read")
            self.lua.pushoptstring(f)
            self.lua.pcall(2, 0)

    def ldef(self, src):
        fhk_pyx_loadmethod(self.lua.L, self.ref, b"ldef")
        self.lua.pushoptstring(src)
        self.lua.pcall(2, 0)

    def query(self, cls):
        cdef list roots = []
        # __annotations__ is created lazily on access, so make sure it's created _before_
        # we iterate over __dict__. otherwise we would modify __dict__ during iteration.
        annotations = cls.__annotations__
        for k,v in cls.__dict__.items():
            if not isinstance(v, root):
                continue
            r = PyxRoot(k)
            roots.append(r)
            if k in annotations:
                ann = annotations[k]
                r.new = ann
                orig = get_origin(ann)
                if orig:
                    args = get_args(ann)
                    if len(args) == 1:
                        r.vec = orig
                        r.new = args[0]
            fhk_pyx_loadmethod(self.lua.L, self.ref, b"setroot")      #< setroot, graph
            lua_pushlightuserdata(self.lua.L, <void*>r)               #< setroot, graph, root
            self.lua.pushoptstring((<root>v).name)                    #< setroot, graph, root, var
            self.lua.pcall(3, 0)
        return QueryFn(self.graph, cls, tuple(roots))

    def add_given(self, var, f, ldef=None):
        sig = signature(f)
        cdef bytes params = b"".join(b"i" if p.annotation == int else b"x" for p in sig.parameters.values())
        ann = sig.return_annotation
        vec, ss = None, False
        if ann is not Signature.empty:
            orig = get_origin(ann)
            if orig and issubclass(orig, tuple):
                args = get_args(ann)
                if len(args) != 2 or not issubsettype(args[1]):
                    raise FhkError("expected return tuple (type, subset)")
                ann, ss = args[0], True
                orig = get_origin(ann)
            if isiterabletype(orig):
                vec = orig
                args = get_args(ann)
                if len(args) == 1:
                    ann = args[0]
        if hasattr(f, "__code__"):
            code = f.__code__
            desc = f"{code.co_name}: ({code.co_filename}:{code.co_firstlineno})"
        else:
            desc = str(f)
        fhk_pyx_loadmethod(self.lua.L, self.ref, b"given")
        self.lua.pushoptstring(var)
        lua_pushlightuserdata(self.lua.L, <void*>f)
        lua_pushstring(self.lua.L, params)
        lua_pushlightuserdata(self.lua.L, <void*>vec)
        lua_pushlightuserdata(self.lua.L, <void*>ann)
        lua_pushboolean(self.lua.L, ss)
        self.lua.pushoptstring(desc)
        self.lua.pushoptstring(ldef)
        self.lua.pcall(9, 0)

    def given(self, *args, **kwargs):
        def deco(f):
            self.add_given(*args, f=f, **kwargs)
            return f
        return deco

    def add_model(self, f, name=None, ldef=None):
        fhk_pyx_loadmethod(self.lua.L, self.ref, b"model")
        lua_pushlightuserdata(self.lua.L, <void*>f)
        self.lua.pushoptstring(name)
        self.lua.pushoptstring(ldef)
        self.lua.pcall(4, 0)

    def model(self, *args, **kwargs):
        def deco(f):
            self.add_model(f, *args, **kwargs)
            return f
        return deco

    def prepare(self):
        fhk_pyx_loadmethod(self.lua.L, self.ref, b"prepare")
        self.lua.pcall(1, 2)
        self.graph.base = <void*> lua_tointeger(self.lua.L, -2)
        self.graph.G = <fhk_graph*> lua_tointeger(self.lua.L, -1)
        lua_pop(self.lua.L, 2)

    def solver(self, mem=None):
        return Solver(self.graph, mem)

    def dump(self, color=False):
        fhk_pyx_loadmethod(self.lua.L, self.ref, b"dump")
        lua_pushboolean(self.lua.L, color)
        self.lua.pcall(2, 1)
        dump = lua_tostring(self.lua.L, -1).decode("utf8")
        lua_pop(self.lua.L, 1)
        return dump

    def sethook(self, hook):
        fhk_pyx_loadmethod(self.lua.L, self.ref, b"sethook")
        self.lua.pushoptstring(hook)
        self.lua.pcall(2, 0)

cdef int setvalue_scatter(fhk_solver *S, int idx, str fmt, object it, fhk_subset ss) except -1:
    fhk_setvalueD(S, idx, ss)
    cdef object mem = fhk_pyx_memV(S, idx).cast(fmt)
    cdef int first
    cdef fhk_pkref pk
    it = iter(it)
    if subset_isIE(ss):
        first = subsetI_first(ss)
        for i in range(subsetIE_size(ss)):
            mem[first+i] = next(it)
    else:
        pk = subsetC_pk(ss)
        while True:
            first = pkref_first(pk)
            for i in range(pkref_size(pk)):
                mem[first+i] = next(it)
            if not pkref_more(pk):
                break
            pk = pkref_next(pk)
    return 0

cdef public int FHK_API_fhk_pyx_setvalue_scatter_space(fhk_solver *S, int idx, str fmt, object it) except -1:
    return setvalue_scatter(S, idx, fmt, it, fhk_pyx_space(S, idx))

cdef public int FHK_API_fhk_pyx_setvalue_scatter2(fhk_solver *S, int idx, str fmt, object rv) except -1:
    return setvalue_scatter(S, idx, fmt, rv[0], tosubset(S, rv[1]))
