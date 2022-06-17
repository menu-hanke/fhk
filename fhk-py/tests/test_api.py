from dataclasses import dataclass
from typing import List, Sequence, Tuple
import pytest
import fhk

def test_read_back_scalar():
    view = fhk.View()
    view.group("a").shape(1)

    @view.given("a#x", ctype="int")
    def _a_x():
        return 123

    class Result:
        x: int = fhk.root("a#x")

    with fhk.Graph(view) as g:
        solver = g.solver(Result)

    assert solver().x == 123

def test_read_back_vector():
    view = fhk.View()
    view.group("a").shape(3)

    @view.given("a#x")
    def _a_x() -> List[float]:
        return [1, 2, 3]

    class Result:
        x: List[float] = fhk.root("a#x")

    with fhk.Graph(view) as g:
        solver = g.solver(Result)

    assert solver().x == [1,2,3]

def test_read_back_subset():
    view = fhk.View()
    view.group("a").shape(3)

    @view.given("a#x")
    def _a_x() -> List[float]:
        return [1, 2, 3]

    class Result:
        x: List[float] = fhk.root("a#x")

    with fhk.Graph(view) as g:
        solver = g.solver(Result)

    r = solver(subset={"x": 1})
    assert r.x == [2]

    r = solver(subset={"x": fhk.interval(0, 3)})
    assert r.x == [1,2,3]

def test_complex_subset():
    view = fhk.View()
    view.group("a").shape(10)

    @view.given("a#x")
    def _a_x(idx: int) -> float:
        return idx

    class Result:
        x: List[float] = fhk.root("a#x")

    with fhk.Graph(view) as g:
        solver = g.solver(Result)

    r = solver(subset={"x": [0, 2,3,4,5,6, 8,9]})
    assert(r.x == [0, 2,3,4,5,6, 8,9])

def test_given_params():
    view = fhk.View()
    view.group("a").shape(1)
    view.group("b").shape(3)

    zs = []

    @view.given("b#z")
    def getz(idx: int) -> float:
        return zs[idx]

    @dataclass
    class State:
        x: float
        ys: List[float]

        @view.given("a#x")
        def getx(self) -> float:
            return self.x

        @view.given("b#y")
        def gety(self, idx: int) -> float:
            return self.ys[idx]

    class Result:
        x: float = fhk.root("a#x")
        y: List[float] = fhk.root("b#y")
        z: List[float] = fhk.root("b#z")

    with fhk.Graph(view) as g:
        solver = g.solver(Result)

    zs.extend([100,200,300])
    r = solver(State(x=1, ys=[2,3,4]))
    assert r.x == 1
    assert r.y == [2, 3, 4]
    assert r.z == [100, 200, 300]

def test_given_subsets():
    view = fhk.View()
    view.group("a").shape(6)

    @dataclass
    class State:
        xs: List[float]

        @view.given("a#x")
        def getxs(self, idx: int) -> Tuple[Sequence[float], fhk.Subset]:
            start = 3*(idx//3)
            return self.xs[start:start+3], fhk.interval(start, 3)

    class Result:
        x: List[float] = fhk.root("a#x")

    with fhk.Graph(view) as g:
        solver = g.solver(Result)

    assert solver(State(xs=[1,2,3,4,5,6])).x == [1,2,3,4,5,6]

def test_shapefunc():
    view = fhk.View()

    @dataclass
    class State:
        xs: List[float]

        @view.shape("a")
        def numa(self) -> int:
            return len(self.xs)

        @view.given("x")
        def getxs(self) -> List[float]:
            return self.xs

    class Result:
        x: List[float] = fhk.root("a#x")

    with fhk.Graph(view) as g:
        solver = g.solver(Result)

    r = solver(State(xs=[1,2,3,4,5]))
    assert r.x == [1,2,3,4,5]

def test_gfile():
    view = fhk.View()
    view.group("a").shape(1)

    class Result:
        x: float = fhk.root("a#x")

    with fhk.Graph(view, "graph.g.lua") as g:
        solver = g.solver(Result)

    assert(solver().x == 123)


def test_model():
    view = fhk.View()
    view.group("a").shape(1)

    @view.given("a#x")
    def _a_x() -> float:
        return 10

    @view.model("a#m", 'params "x", returns "y" *as "double"')
    def _a_m(x: float) -> float:
        return x**2

    class Result:
        y: float = fhk.root("a#y")

    with fhk.Graph(view) as g:
        solver = g.solver(Result)

    assert solver().y == 100

def test_map():
    view = fhk.View()
    view.group("a").shape(3)

    @view.map("const_0", scalar=True)
    def const_0() -> fhk.Subset:
        return 0

    @const_0.inverse("invconst_0")
    def invconst_0() -> fhk.Subset:
        return fhk.interval(0, 3)

    @view.map("next", scalar=True)
    def next(idx: int) -> fhk.Subset:
        return (idx+1)%3

    @next.inverse("prev", scalar=True)
    def prev(idx: int) -> fhk.Subset:
        return (idx+2)%3

    @view.given("a#x")
    def _a_x() -> List[float]:
        return [3, 2, 1]

    @view.model("a#m", 'params {"x" *choose "const_0", "x" *choose "next"}, returns "y" *as "double"')
    def _a_m(a: float, b: float) -> float:
        return a*b

    class Result:
        y: List[float] = fhk.root("a#y")

    with fhk.Graph(view) as g:
        solver = g.solver(Result)

    assert solver().y == [3*2, 3*1, 3*3]

def test_reuse_mem():
    view = fhk.View()
    view.group("a").shape(1)

    @dataclass
    class State:
        x: int

        @view.given("a#x")
        def getx(self) -> int:
            return self.x

    class Result:
        x: int = fhk.root("a#x")

    with fhk.Graph(view) as g:
        solver = g.solver(Result)

    mem = fhk.Mem()
    assert solver(State(1), mem=mem).x == 1
    mem.reset()
    assert solver(State(2), mem=mem).x == 2

def test_labels():
    view = fhk.View()
    view.group("a").shape(1)
    view.label(pine=1, spruce=2)

    @view.given("a#s", ctype="uint8_t")
    def _a_s() -> int:
        return 1

    @view.model("a#m1", 'check "a#s" *is "pine", returns "a#x" *as "double"')
    def _a_m1():
        return 1

    @view.model("a#m2", 'check "a#s" *is "spruce", returns "a#x" *as "double"')
    def _a_m2():
        return 2

    class Result:
        x: float = fhk.root("a#x")

    with fhk.Graph(view) as g:
        solver = g.solver(Result)

    assert solver().x == 1

def test_lua_errors():
    view = fhk.View()
    view.group("a").shape(1)

    class Result:
        x: float = fhk.root("a#x")

    with pytest.raises(fhk.LuaError) as e:
        with fhk.Graph(view) as g:
            g.solver(Result)

    assert "no chain with finite cost" in str(e.value)

def test_invalid_given():
    view = fhk.View()
    view.group("a").shape(1)

    @view.given("a#x")
    def _a_x() -> float: # type: ignore
        pass

    class Result:
        x: float = fhk.root("a#x")

    with fhk.Graph(view) as g:
        solver = g.solver(Result)

    with pytest.raises(fhk.LuaError) as e:
        solver()

    assert "python error" in str(e.value)
    assert "must be real number, not NoneType" in str(e.value)

def test_python_raises():
    view = fhk.View()
    view.group("a").shape(1)

    @view.given("a#x")
    def _a_x() -> float:
        raise RuntimeError("something happened")

    class Result:
        x: float = fhk.root("a#x")

    with fhk.Graph(view) as g:
        solver = g.solver(Result)

    with pytest.raises(fhk.LuaError) as e:
        solver()

    assert "python error" in str(e.value)
    assert "something happened" in str(e.value)

def test_invalid_return_annotation():
    view = fhk.View()
    view.group("a").shape(1)

    with pytest.raises(TypeError) as e:
        @view.given("a#x")
        def _a_x() -> Tuple[int, float]:
            raise NotImplementedError

    assert "second return value must be a subset type" in str(e.value)
