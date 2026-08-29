"""Base classes for cells and cell exceptions"""
from abc import ABCMeta, abstractmethod
from typing import Iterable, Iterator
from itertools import chain, islice

from . import WithItems
from ..equality import Eq
from ..proven import ValidationError

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

    def param(self):
        return Param((self,))

    def is_subobject(self, obj: 'Obj'):
        return self == obj

    def restrict(self, mor: 'Mor'):
        return mor

    def verify(self, e: Eq['Mor']) -> bool:
        return False

    def incl(self) -> 'Mor':
        return Composition(self)

    # def intersection(self, obj: 'Obj') -> tuple['Obj', Iterable[tuple['Mor', 'Mor']]]:
    #     if obj.is_subobject(self):
    #         return obj, ()

    #     raise ValidationError("Can't intersect")

class Mor(metaclass=ABCMeta):
    """Base class for morphisms"""
    # This needs to be hashable, so that we can find equalities.
    __slots__ = 'name', 'source', 'target'#, 'broken'
    name: str
    source: Obj
    target: Obj
    #broken: bool

    # def lower(self):
    #     # We don't support lowering directly to an equalizer because
    #     # of the type-checking involved, which can be handled by `variadic.lift`.
    #     return Composition.strict((self.target.incl(), self))

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
        # We prioritize any value set by subclass initialization.
        #self.broken = getattr(self, 'broken', False)

    def __repr__(self):
        return f'{type(self).__name__}({self.name}: {self.source} -> {self.target})'

    # def iter_set_broken(self, factors: Iterable['Mor']):
    #     for factor in factors:
    #         self.broken = self.broken or factor.broken
    #         yield factor

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

        raise ValueError('`factors` must be an instance of `Obj` if there are no factors.')

    def __init__(self, factors: Obj | Iterable[Mor], _allow_single_factor: bool = False):
        # Do not directly call class for instantiation, use `identity` or
        # `simplified` instead.
        #self.broken = False
        if isinstance(factors, Obj):
            self.factors = []
            super().__init__(factors, factors)
            self.frozen = True
            return

        #it = self.iter_set_broken(factors)
        it = iter(factors)
        self.factors = self._reuse_first(it)
        f = self.factors
        if f:
            # Pop last factor so that it can be reduced.
            tail = chain((f.pop(),), it)
        else:
            tail = it

        f.extend(_reduce_factors(_flatten_factors(tail)))
        self.frozen = True

        if len(f) == 1 and not _allow_single_factor:
            raise ValueError('Single factor')

        target = f[0].target
        source = f[-1].source
        super().__init__(source, target)

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

#T = TypeVar('T')
#Components = Iterable[tuple[str, T] | T]

class Param(WithItems[Obj]):
    __slots__ = ('components', 'label_to_idx_map')
    components: tuple[Obj, ...]
    label_to_idx_map: tuple[tuple[str, int], ...]

    def __init__(self, components: Iterable[tuple[str, Obj] | Obj]):
        li_map: list[tuple[str, int]] = []
        comps: list[Obj] = []

        for i, c in enumerate(components):
            if isinstance(c, tuple):
                label, c = c
                li_map.append((label, i))

            comps.append(c)

        self.label_to_idx_map = tuple(li_map)
        self.components = tuple(comps)

    def getitem(self, idx: int):
        return self.components[idx]

    def __len__(self):
        return len(self.components)

    def __eq__(self, x: object):
        return self is x or (
            isinstance(x, type(self))
            and self.components == x.components
            and self.label_to_idx_map == x.label_to_idx_map
        )

    def labels(self):
        res: list[str] = ['']*len(self.components)
        for l, i in self.label_to_idx_map:
            res[i] = l

        return res

class Parallel(WithItems[tuple[Mor, Mor]]):
    __slots__ = ('source', 'pairs', '_sources')
    source: Obj
    pairs: tuple[tuple[Mor, Mor], ...]
    _sources: tuple[tuple[Obj, Obj], ...]

    def __init__(self, source: Obj, pairs: Iterable[tuple[Mor, Mor]]):
        # Lifting an inclusion based on builtin subset operation
        # has the only disadvantage that it cannot rely on intensional equalities.
        # The `Parallel` class avoids having to compose with an inclusion, whose
        # target might end up being discarded, and which has to be removed when
        # normalizing the requirement.
        # Extending here is correct since the common source is already determined.
        self._sources = tuple((i.source, j.source) for i, j in pairs)
        self.pairs = tuple((i.extend(), j.extend()) for i, j in pairs)
        self.source = source

    def is_valid(self):
        source = self.source
        for si, sj in self._sources:
            if not (source.is_subobject(si) and source.is_subobject(sj)):
                raise ValidationError('`source` must be subobject.')

        for i, j in self.pairs:
            # Recall that there is no such thing as a public eq which need to be checked
            # by the public interface.
            if i.target != j.target:
                raise ValidationError('Must have equal targets')

    def getitem(self, idx: int):
        i, j = self.pairs[idx]
        return (
            self.source.restrict(i),
            self.source.restrict(j),
        )

    def __len__(self):
        return len(self.pairs)

    def __eq__(self, x: object):
        return self is x or (
            isinstance(x, type(self))
            and self.source == x.source
            and self.pairs == x.pairs
        )
