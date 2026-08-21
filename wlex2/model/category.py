"""Base classes for cells and cell exceptions"""
from abc import ABCMeta, abstractmethod
from typing import Iterable, Iterator
from itertools import chain, islice

from . import WithItems
from ..equality import Eq

def _flatten_factors(factors: Iterable['Mor']) -> Iterator[tuple['Mor', bool]]:
    # All compositions must be flat!
    for factor in factors:
        if isinstance(factor, Composition):
            # It is fair to assume that `factor.factors` is already flattened
            f = factor.factors
            for i in range(len(f) - 1):
                yield f[i], False

            yield f[-1], True
        else:
            yield factor, True

def _reduce_factors(factors: Iterator[tuple['Mor', bool]]) -> Iterator['Mor']:
    for prev, pr in factors:
        break
    else:
        assert False

    for factor, fr in factors:
        if pr:
            reduced = prev.reduce(factor)
        else:
            reduced = None

        if reduced is None:
            yield prev
            prev = factor
            pr = fr
        else:
            prev = reduced
            # pr remains True

    yield prev

class Obj(metaclass=ABCMeta):
    """Base class for objects"""
    __slots__ = ('name',)
    name: str

    @abstractmethod
    def accepts(self, x: object) -> bool:
        """`self` accepts `x` as element."""
        # `accepts` may require verication of equalities in subclass,
        # specifically in equalizers. In this case `self` is the source
        # of the equalities.

    def __init__(self):
        self.name = ''

    def __repr__(self):
        return f'{type(self).__name__}({self.name})'

    def parallel(self):
        return Parallel(self, ())

    def is_subobject(self, obj: 'Obj'):
        return self == obj

    def verify(self, e: Eq['Mor']) -> bool:
        return False

class Mor(metaclass=ABCMeta):
    """Base class for morphisms"""
    # This needs to be hashable, so that we can find equalities.
    __slots__ = 'name', 'source', 'target'
    name: str
    source: Obj
    target: Obj

    def extend(self):
        return self

    @abstractmethod
    def ev(self, x: object) -> object:
        """Element, to which morphism `self` maps `x`"""

    def ev_eq(self, eq: Eq[object]):
        return eq.apply(self.ev)

    def reduce(self, mor: 'Mor') -> 'Mor | None':
        """Simplify with next factor"""
        # Last factor of composition gets passed the identity as argument.
        # Reducing with an inclusion within a lift requires simply getting the next factor
        # into the lift as if by naturality. Same applies to projections and pairings by
        # the naturality of the diagonal.

    def __init__(self, source: Obj, target: Obj):
        self.name = ''
        self.source = source
        self.target = target

    def __repr__(self):
        return f'{type(self).__name__}({self.name}: {self.source} -> {self.target})'

class Composition(Mor):
    """Models the result of `category.compose`"""
    __slots__ = 'factors', 'frozen'
    factors: list[Mor]
    frozen: bool # Referenced (named) compositions have to be frozen.

    def extend(self):
        factors = self.factors
        if not factors:
            return self

        last = factors[-1]
        ext = last.extend()
        if ext is last:
            return self

        res = Composition(
            chain(
                islice(factors, len(factors) - 1),
                (ext,),
            ),
            _allow_single_factor=True,
        )
        res.name = self.name

        if len(res.factors) == 1:
            return res.factors[0]

        return res

    @classmethod
    def _reuse_first(cls, factors: Iterator[Mor]) -> list[Mor]:
        for factor in factors:
            if isinstance(factor, Composition) and not factor.frozen:
                res = factor.factors
                del factor.factors
                return res

            return [factor]

        return []

    def __init__(self, factors: Obj | Iterable[Mor], _allow_single_factor: bool = False):
        # Do not directly call class for instantiation, use `identity` or
        # `simplified` instead.
        if isinstance(factors, Obj):
            self.factors = []
            super().__init__(factors, factors)
            self.frozen = True
            return

        it = iter(factors)
        self.factors = self._reuse_first(it)
        f = self.factors
        if f:
            # Pop last factor so that it can be reduced.
            tail = chain((f.pop(),), it)
        else:
            tail = it

        self.factors.extend(_reduce_factors(_flatten_factors(tail)))
        self.frozen = True

        if f:
            if len(f) == 1 and not _allow_single_factor:
                raise ValueError('Single factor')

            target = f[0].target
            source = f[-1].source
            super().__init__(source, target)
        else:
            raise ValueError('`factors` must be an instance of `Obj` if there are no factors.')

    @classmethod
    def strict(cls, factors: Obj | Iterable[Mor]):
        res = cls(factors, _allow_single_factor=True)
        if len(res.factors) == 1:
            return res.factors[0]

        return res

    def ev(self, x: object):
        res = x
        for factor in reversed(self.factors):
            res = factor.ev(res)

        return res

    def __eq__(self, x: object):
        return self is x or (
            isinstance(x, type(self))
            and self.source == x.source
            and self.factors == x.factors
        )

class Parallel(WithItems[tuple[Mor, Mor]]):
    __slots__ = ('source', 'pairs')
    source: Obj
    pairs: tuple[tuple[Mor, Mor], ...]

    def __init__(self, source: Obj, pairs: Iterable[tuple[Mor, Mor]]):
        # Lifting an inclusion based on builtin subset operation
        # has the only disadvantage that it cannot rely on intensional equalities.
        # The `Parallel` class avoids having to compose with an inclusion, whose
        # target might end up being discarded, and which has to be removed when
        # normalizing the requirement.
        self.pairs = tuple(pairs)
        self.source = source

        for i, j in self.pairs:
            if not (source.is_subobject(i.source) and source.is_subobject(j.source)):
                raise ValueError('`source` must be subobject.')

            # Recall that there is no such thing as a public eq which need to be checked
            # by the public interface. Initialization should already ensure that the equalities
            # are fulfilled.
            if i.target != j.target:
                raise ValueError('Must have the equal targets')

    def getitem(self, idx: int) -> tuple[Mor, Mor]:
        raise NotImplementedError

    def __len__(self):
        return len(self.pairs)

    def __eq__(self, x: object):
        return self is x or (
            isinstance(x, type(self))
            and self.source == x.source
            and self.pairs == x.pairs
        )
