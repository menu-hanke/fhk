from typing import Any, Iterable, Protocol, Type, Union

__all__ = (
    "Subset",
    "EMPTYSET"
)

Subset = Union[int, Iterable[int]]
EMPTYSET = -1

def issubsettype(t: Type) -> bool:
    return issubclass(t, int) or issubclass(t, Iterable)

class Conv(Protocol):
    def init(self, typecode: str): ...
    def set(self, mem: memoryview, ss: int): ...
    def get(self) -> Any: ...
