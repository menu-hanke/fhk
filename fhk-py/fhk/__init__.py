import dataclasses
import functools
import inspect
from collections.abc import Iterable
from types import GenericAlias
from typing import Any, Callable, Dict, Generic, List, Optional, Protocol, Sequence, Tuple, Type, TypeVar, Union, get_args, get_origin, overload
from fhk._ctypes import CRoot, GCDriver, GCLua, GCMem, GCPin, GCSolver as Solver, init, newlua, ready, solve

#---- subsets ----------------------------------------
from fhk._ctypes import (
    interval as interval_,
    space as space_
)

interval: Callable[[int, int], int] = interval_
space: Callable[[int], int] = space_

Subset = int
EMPTYSET: Subset = -1

def issubsettype(t: Type) -> bool:
    return issubclass(t, int)

class ToLua(Protocol):
    def __lua__(self, lua: GCLua) -> Any:
        ...

class Push:
    __slots__ = "__lua__"
    def __init__(self, f: Callable[[GCLua], Any]):
        self.__lua__ = staticmethod(f)

T = TypeVar("T", bound=Type)
C = TypeVar("C", bound=Callable)
CI = TypeVar("CI", bound=Callable[...,int])
CS = TypeVar("CS", bound=Callable[...,Subset])
U = TypeVar("U")

LuaCallable = Union[ToLua, GCPin]
Multi = Tuple[Iterable[U], Subset]

def spacevar(f: Callable[...,Sequence[U]]) -> Callable[...,Multi[U]]:
    @functools.wraps(f)
    def w(*args):
        v = f(*args)
        return v, interval(0, len(v))
    if "return" in f.__annotations__:
        w.__annotations__["return"] = GenericAlias(Tuple, (f.__annotations__["return"], Subset))
    return w

#---- python <-> c ----------------------------------------

PY_PRIMITIVES = { float: "double", int: "int" }

@dataclasses.dataclass
class CTypeAnnotation:
    cts: str
    vector: Optional[Type]

def _infer_ctype(ann: Type) -> Optional[CTypeAnnotation]:
    orig = get_origin(ann)
    if orig:
        args = get_args(ann)
        if len(args) > 0:
            ct = PY_PRIMITIVES.get(args[0])
            if orig and ct:
                return CTypeAnnotation(cts=ct, vector=orig)
    else:
        ct = PY_PRIMITIVES.get(ann)
        if ct:
            return CTypeAnnotation(cts=ct, vector=None)

def _vref_cta(f: Callable) -> Optional[CTypeAnnotation]:
    rt = inspect.signature(f).return_annotation
    if rt is inspect.Signature.empty:
        return None
    if get_origin(rt) in (Tuple, tuple):
        args = get_args(rt)
        if len(args) != 2 or not issubsettype(args[1]):
            raise ValueError(f"unexpected return type: {rt}")
        cta = _infer_ctype(args[0])
        if (not cta) or (not cta.vector):
            raise ValueError(f"expected vector return ctype: {args[0]}")
    else:
        cta = _infer_ctype(rt)
        if (not cta) or cta.vector:
            raise ValueError(f"expected scalar return ctype: {rt}")
    return cta

def _cta_encode(cta: Optional[CTypeAnnotation]) -> str:
    if cta:
        return f"{cta.cts}{']' if cta.vector else ''}"
    else:
        return ""

# i -> instance
# x -> state
def _param_def(f: Callable) -> str:
    params = inspect.signature(f).parameters
    out = ""
    for p in params.values():
        if p.annotation == int:
            out += "i"
        elif "x" in out:
            raise ValueError(f"unexpected parameter: {p}")
        else:
            out += "x"
    return out

def _wrap_params(f: Callable, pd: str) -> Callable:
    old = _param_def(f)
    if old == pd:
        return f
    @functools.wraps(f)
    def w(*args):
        kw = dict(zip(pd,args))
        return f(*(kw[c] for c in old))
    return w

#---- python rules ----------------------------------------

def group(name: str, *rules: Any) -> Push:
    return Push(lambda lua: lua.fhk_py.rules.group(name, *rules)[0])

def shape(s: Any) -> Push:
    return Push(lambda lua: lua.fhk_py.shape(s)[0])

def _pyvirt(name: str, f: Any, cta: Optional[CTypeAnnotation], copy: bool) -> Push:
    return Push(lambda lua: lua.fhk_py.pyvirt(
        name,
        _wrap_params(f, "xi"),
        f"{'!' if copy else ''}{str(_cta_encode(cta))}",
    )[0])

def virtual(name: str, f: Callable, copy: bool) -> Push:
    return _pyvirt(name, f, _vref_cta(f), copy)

def anymap(name: str, inverse: str, f: Callable, scalar: bool) -> Push:
    flags = f"{'i' if 'i' in _param_def(f) else 'k'}{'s' if scalar else 'v'}"
    return Push(lambda lua: lua.fhk_py.pymap(
        name,
        inverse,
        flags,
        _wrap_params(f, "k" in flags and "x" or "xi")
    )[0])

#---- solving ----------------------------------------

class SolverFn(Generic[T]):
    _driver: GCDriver
    _result: Type
    _roots: List[CRoot]

    def __call__(
        self,
        state: Any = None,
        solver: Optional[Solver] = None,
        subset: Dict[str, Subset] = {}
    ) -> T:
        if solver is None:
            solver = init(self._driver, GCMem(), state)
        result = self._result()
        solve(self._driver, solver, self._roots, subset, state, result)
        return result

@dataclasses.dataclass
class Root:
    name: str
    cts: Optional[str]

# this only exists to satisfy type checkers, ie. so that callers can do
# class Result:
#     x: float = root("a#x")
# and have it pass typecheck.
def root(name: str, cts: Optional[str] = None) -> Any:
    return Root(name=name, cts=cts)

@dataclasses.dataclass
class GenRoot:
    name: str
    vector: Optional[Type]
    ref: GCPin

@dataclasses.dataclass
class GenSolver:
    fn: SolverFn
    roots: List[GenRoot]

def _def_solver(lua: GCPin, state: GCPin, result: Type) -> GenSolver:
    roots = []
    for k,v in result.__dict__.items():
        if not isinstance(v, Root):
            continue
        if v.cts:
            # need to be careful about type conversions here, eg. float -> int
            # (we can't use a direct buffer in that case).
            # maybe that should just not be allowed?
            raise NotImplementedError("TODO")
        if k in result.__annotations__:
            ann = result.__annotations__[k]
            cta = _infer_ctype(ann)
            if not cta:
                raise ValueError(f"unrepresentable ctype: {ann}")
        else:
            # no typehint, we'll use whatever we get from the graph.
            cta = None
        ref, = lua.setroot(state, v.name, cta and cta.cts)
        roots.append(GenRoot(k, cta and cta.vector, ref))
    fn = SolverFn()
    fn._result = result
    return GenSolver(fn, roots)

@dataclasses.dataclass
class PendingMapDef:
    view: "View"
    name: str
    scalar: bool
    f: Callable

    def inverse(self, name: str, scalar: bool = False) -> Callable[[CS], CS]:
        def deco(f):
            self.view.append(anymap(self.name, name, self.f, self.scalar))
            self.view.append(anymap(name, self.name, f, scalar))
            return f
        return deco

class View(list[LuaCallable]):

    def __lua__(self, lua: GCLua) -> GCPin:
        return lua.fhk_py.rules.composite(*self)[0]

    def group(self, name: str) -> "View":
        v = View()
        self.append(group(name, v))
        return v

    @overload
    def shape(self, x: str) -> Callable[[CI], CI]: ...
    @overload
    def shape(self, x: Union[int,Callable[..., int]]) -> None: ...

    def shape(self, x):  # type: ignore
        if isinstance(x, str):
            def deco(f):
                self.append(group(x, shape(f)))
                return f
            return deco
        else:
            self.append(shape(x))

    def given(self, name: str, copy: bool = True) -> Callable[[C], C]:
        def deco(f):
            self.append(virtual(name, f, copy))
            return f
        return deco

    @overload
    def map(self, name: str, inverse: None = None, scalar: bool = False) -> Callable[[Callable[...,Subset]], PendingMapDef]: ...
    @overload
    def map(self, name: str, inverse: str, scalar: bool = False) -> Callable[[CS], CS]: ...

    def map(self, name, inverse=None, scalar=False): # type: ignore
        if inverse is None:
            def deco(f): # type: ignore
                return PendingMapDef(self, name, scalar, f)
            return deco
        else:
            def deco(f): # type: ignore
                self.append(anymap(name, inverse, f, scalar))
                return f
            return deco

# TODO this should be a context manager?
class Graph:
    _lua: GCPin
    _solvers: List[GenSolver]

    def __init__(self, *args: Union[LuaCallable, str], _lua: GCPin = None):
        if _lua is None:
            _lua = newlua()
        self._lua = _lua
        self._solvers = []
        views, graphs = [], []
        for x in args:
            (graphs if isinstance(x, str) else views).append(x)
        self._state, = _lua.rules.newstate(View(*views))
        self.include(*graphs)

    def solver(self, result: T) -> SolverFn[T]:
        s = _def_solver(self._lua, self._state, result)
        self._solvers.append(s)
        return s.fn

    def include(self, *files: str):
        self._lua.rules.read(self._state, *files)

    def __enter__(self) -> "Graph":
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.ready()

    def ready(self):
        d = ready(self._state)
        for s in self._solvers:
            fn = s.fn
            fn._driver = d
            roots = []
            for r in s.roots:
                idx, fmt = self._lua.getroot(r.ref)
                roots.append(CRoot(name=r.name, vector=r.vector, idx=idx, fmt=fmt))
            fn._roots = roots
