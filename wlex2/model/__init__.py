from abc import ABCMeta, abstractmethod
from typing import Sequence, overload

class WithItems[T](Sequence[T], metaclass=ABCMeta):
    @overload
    def __getitem__(self, idx: int) -> T: ...
    @overload
    def __getitem__(self, idx: slice) -> Sequence[T]: ...

    def __getitem__(self, idx: int | slice) -> T | Sequence[T]:
        if isinstance(idx, slice):
            start, stop, step = idx.indices(len(self))
            return tuple(self.getitem(i) for i in range(start, stop, step))

        return self.getitem(idx)

    @abstractmethod
    def getitem(self, idx: int) -> T:
        """Get item"""
