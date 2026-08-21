from typing import Callable, Collection, Iterator, NamedTuple, Self, TypeGuard

from . import is_tuple

class Eq[T](NamedTuple):
    s: T
    t: T

    def __and__(self, eq: 'Eq[T]'):
        # trans
        # Polish order
        if self.t == eq.s:
            return type(self)(self.s, eq.t)

        raise ValueError('No match')

    def __invert__(self):
        # sym. Needed for trans.
        return type(self)(self.t, self.s)

    def apply[S](self, fn: Callable[[T], S]):
        return Eq(fn(self.s), fn(self.t))

    @classmethod
    def from_tuple(cls, *eqs: Self | T):
        # There is no to_tuple. We use apply on getitem/projection.
        def _is_eq(x: Self | T) -> TypeGuard[Eq[T]]:
            return isinstance(x, Eq)

        def _is_t(x: Self | T) -> TypeGuard[T]:
            return not isinstance(x, Eq)

        s: list[T] = []
        t: list[T] = []

        for eq in eqs:
            if _is_eq(eq):
                s.append(eq.s)
                t.append(eq.t)
            else:
                assert _is_t(eq)
                s.append(eq)
                t.append(eq)

        return Eq(tuple(s), tuple(t))

class Verifier[T](Collection[Eq[T]]):
    __slots__ = ('_proofs',)
    _proofs: set[Eq[T]]

    def __init__(self, proofs: set[Eq[T]]):
        self._proofs = proofs

    def __contains__(self, x: object) -> bool:
        if not (is_tuple(x) and len(x) == 2):
            return False

        s, t = x
        assert isinstance(s, object)
        assert isinstance(t, object)
        return (
            s == t
            or (s, t) in self._proofs
            or (t, s) in self._proofs
            or (
                is_tuple(s) and is_tuple(t) and len(s) == len(t)
                and all((i, j) in self for i, j in zip(s, t))
            )
            or _check_equalizer((s, t))
        )

    def __iter__(self) -> Iterator[Eq[T]]:
        return iter(self._proofs)

    def __len__(self) -> int:
        return len(self._proofs)

def _check_equalizer(e: Eq[object]):
    from .model.category import Mor

    s, t = e
    if isinstance(s, Mor) and isinstance(t, Mor):
        return s.source.verify(Eq(s, t))

    return False
