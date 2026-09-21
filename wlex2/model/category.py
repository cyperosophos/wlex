"""Base classes for cells and cell exceptions"""
from abc import ABCMeta, abstractmethod
from typing import Iterator

from ..equality import Eq

class InclError(ValueError):
    pass

class ProjError(ValueError):
    pass

ProjNode = tuple[int, 'ProjTree']
ProjTree = ProjNode | tuple[ProjNode, ...] # () is identity
# -1 is for `pack`, distinguish pairing of single projection from projection.

def _reduce_factors(prev: 'Mor', factors: Iterator['Mor']) -> Iterator['Mor']:
    for factor in factors:
        reduced = prev.reduce(factor)
        if reduced is None:
            yield prev
            yield factor
            yield from factors
        else:
            prev = reduced

    yield prev

class Obj(metaclass=ABCMeta):
    """Base class for objects"""
    __slots__ = ('name',)
    name: str

    @property
    def univ(self):
        return self

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

    # def parallel(self):
    #     i = Composition(self)
    #     return Parallel(self, (i, i))

    # def param(self):
    #     return Param((self,))

    def is_subobject(self, obj: 'Obj'):
        return self == obj

    def restrict(self, mor: 'Mor'):
        return mor

    def verify(self, e: Eq['Mor']) -> bool:
        return False

    def incl(self, target: 'Obj | None') -> 'Mor':
        if self == target:
            return Composition(self)

        raise InclError

    def component(self, idx: int) -> 'Obj':
        raise ProjError

    def pack(self, source: 'Obj') -> 'Mor':
        raise ProjError

    def proj(self, target: 'Obj | int') -> 'Mor':
        if isinstance(target, int):
            raise ProjError

        if self == target:
            return Composition(self)

        return target.pack(self)

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

    # def lift(self, target: Obj):
    #     if self.target == target:
    #         return self

    #     raise ValueError("Can't lift")

    def incl(self, target: Obj | None = None):
        return Composition.strict(
            self.target.incl(target),
            self,
        )

    def proj(self, target: Obj | int):
        return Composition.strict(
            self.target.proj(target),
            self,
        )

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
    __slots__ = 'factors', 'length', 'f', 'g'
    factors: list[Mor]
    length: int
    f: Mor
    g: Mor

    def extend(self):
        f = self.f
        g = self.g
        ext_g = g.extend()
        if ext_g is g:
            return self

        return Composition.strict(f, ext_g)

    @classmethod
    def _first_factors(cls, factor: Mor) -> list[Mor]:
        if isinstance(factor, Composition):
            factors = factor.factors
            if factor.length == len(factors):
                return factors

            return factors[:]

        return [factor]

    def __init__(self, factors: Obj | tuple[Mor, Mor]):
        # Do not directly call class for instantiation, use `identity` or
        # `simplified` instead.
        if isinstance(factors, Obj):
            self.factors = []
            super().__init__(factors, factors)
            self.length = 0
            return

        f, g = factors
        ff = self._first_factors(f)
        if isinstance(g, Composition):
            tail = g.factors
        else:
            tail = (g,)

        if ff:
            f0 = self.factors.pop() # Not Composition
            tail = _reduce_factors(f0, iter(tail))

        ff.extend(tail)
        self.length = len(ff)
        target = ff[0].target
        source = ff[-1].source
        self.factors = ff
        self.f = f
        self.g = g
        super().__init__(source, target)

    @classmethod
    def strict(cls, f: Mor, g: Mor) -> Mor:
        res = cls((f, g))
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
            and eq_with_length(
                self.factors, self.length,
                x.factors, x.length,
            )
        )

    def __hash__(self):
        # TODO: Check that the length pattern is being used everywhere where it's needed.
        return hash((self.source, *zip(self.factors, range(self.length))))

def eq_with_length[T](l1: list[T], len1: int, l2: list[T], len2: int):
    return (
        len1 == len2
        and all(
            i == j for i, j, _
            in zip(l1, l2, range(len1))
        )
    )
