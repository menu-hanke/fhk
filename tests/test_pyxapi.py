from dataclasses import dataclass
from typing import Sequence
import pytest
import fhk

def test_read_back_scalar():
    with fhk.Graph() as g:
        @g.given("x")
        def getx():
            return 123
        @g.query
        class query:
            x: int = fhk.root("x")
    assert query().x == 123

def test_read_back_vector():
    with fhk.Graph() as g:
        @g.given("g")
        def getg():
            return fhk.interval1(3)
        @g.given("g#x")
        def getx() -> list[float]:
            return [1,2,3]
        @g.query
        class query:
            x: list[float] = fhk.root("g#x")
    assert query().x == [1,2,3]

def test_read_back_subset():
    with fhk.Graph() as g:
        @g.given("g")
        def getg():
            return fhk.interval1(3)
        @g.given("g#x")
        def getx() -> list[float]:
            return [1,2,3]
        @g.query
        class query:
            x: list[float] = fhk.root("g#x")
    assert query(subsets={"x":1}).x == [2] # type: ignore
    assert query(subsets={"x":fhk.interval1(3)}).x == [1,2,3] # type: ignore

def test_complex_subset():
    with fhk.Graph() as g:
        @g.given("g")
        def getg():
            return fhk.interval1(10)
        @g.given("g#x")
        def getx(i: int) -> float:
            return i
        @g.query
        class query:
            x: list[float] = fhk.root("g#x")
    assert query(subsets={"x": [0, 2,3,4,5,6, 8,9]}).x == [0, 2,3,4,5,6, 8,9] # type: ignore

def test_given_params():
    g = fhk.Graph()
    zs = []

    @g.given("g")
    def getg() -> fhk.Subset:
        return fhk.interval1(3)

    @g.given("g#z")
    def getz(i: int) -> float:
        return zs[i]

    @dataclass
    class State:
        x: float
        ys: list[float]

        @g.given("x")
        def getx(self) -> float:
            return self.x

        @g.given("g#y")
        def gety(self, i: int) -> float:
            return self.ys[i]

    @g.query
    class query:
        x: float = fhk.root("x")
        y: list[float] = fhk.root("g#y")
        z: list[float] = fhk.root("g#z")

    g.prepare()
    zs.extend([100,200,300])
    r = query(State(x=1, ys=[2,3,4])) # type: ignore
    assert r.x == 1
    assert r.y == [2, 3, 4]
    assert r.z == [100, 200, 300]

def test_given_subsets():
    g = fhk.Graph()

    @g.given("g")
    def getg():
        return fhk.interval1(6)

    @dataclass
    class State:
        xs: list[float]

        @g.given("g#x")
        def getxs(self, idx: int) -> tuple[Sequence[float], fhk.Subset]:
            start = 3*(idx//3)
            return self.xs[start:start+3], fhk.interval1(start, 3)

    @g.query
    class query:
        x: list[float] = fhk.root("g#x")

    g.prepare()
    assert query(State(xs=[1,2,3,4,5,6])).x == [1,2,3,4,5,6] # type: ignore

def test_gfile():
    with fhk.Graph("example.g.lua") as g:
        @g.given("x")
        def getx():
            return 2
        @g.given("b")
        def getb():
            return fhk.interval1(4)
        @g.given("b#y")
        def gety(i: int):
            return i**2
        @g.given("m")
        def getm():
            return fhk.interval1(4)
        @g.query
        class query:
            z: float = fhk.root("z")
            w: float = fhk.root("w")
    r = query()
    assert r.z == 0 + 1 + 4 + 9
    assert r.w == 2 * (0 + 1 + 4 + 9)

def test_model():
    with fhk.Graph() as g:
        @g.given("x")
        def getx():
            return 10
        @g.model(ldef="params 'x', returns 'y'")
        def mod(x: float) -> float:
            return x**2
        @g.query
        class query:
            y = fhk.root("y")
    assert query().y == 10**2

def test_reuse_mem():
    g = fhk.Graph()

    @dataclass
    class State:
        x: int

        @g.given("x")
        def getx(self) -> int:
            return self.x

    @g.query
    class query:
        x: int = fhk.root("x")

    g.prepare()
    mem = fhk.Mem()
    assert query(State(1), mem=mem).x == 1 # type: ignore
    mem.reset()
    assert query(State(2), mem=mem).x == 2 # type: ignore

def test_reuse_solver():
    num = 0
    with fhk.Graph() as g:
        @g.given("x")
        def getx():
            nonlocal num
            num += 1
            return num
        @g.query
        class query:
            x: float = fhk.root("x")
    solver = g.solver()
    assert query(solver=solver).x == 1 # type: ignore
    assert query(solver=solver).x == 1 # type: ignore

def test_lua_errors():
    g = fhk.Graph()

    @g.query
    class query:
        x: float = fhk.root("x")

    with pytest.raises(fhk.FhkError) as e:
        g.prepare()

    assert "object is skipped" in str(e.value)

def test_python_raise():
    with fhk.Graph() as g:
        @g.given("x")
        def getx():
            raise RuntimeError("something happened")
        @g.query
        class query:
            x: float = fhk.root("x")

    with pytest.raises(fhk.FhkError) as e:
        query()

    assert "python error" in str(e.value)
    assert "something happened" in str(e.value)

def test_invalid_return_annotation():
    g = fhk.Graph()

    with pytest.raises(fhk.FhkError) as e:
        @g.given("x")
        def getx() -> tuple[int, float]:
            raise NotImplementedError

    assert "expected return tuple (type, subset)" in str(e.value)

def test_unprepared_graph():
    g = fhk.Graph()

    @g.query
    class query:
        pass

    with pytest.raises(fhk.FhkError) as e:
        query()

    assert "graph is null" in str(e.value)
