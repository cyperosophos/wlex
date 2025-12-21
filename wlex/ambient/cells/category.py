"""Category cell classes"""
from typing import override, Callable
from abc import ABCMeta
from collections.abc import Sequence

from ..cells import Obj, Mor, PrimMor, Eq, PrimEq

class CategoryObj(Obj, metaclass=ABCMeta):
    """Models object `category.Obj`"""
    __slots__ = ()

    _composition_cls: type['Composition']

    @classmethod
    def init_cls(cls):
        cls._composition_cls = Composition

    @override
    def identity(self):
        return self._composition_cls.identity(self)

    @override
    @classmethod
    def vcomposition(cls, *factors: Mor) -> Mor:
        return cls._composition_cls.simplified(factors)

class CategoryMor(Mor, metaclass=ABCMeta):
    """Models object `category.Mor`"""
    __slots__ = ()

    @override
    def ref(self):
        eq = Eq(self, self)
        eq.proven = True
        return eq

    @override
    def compose(self, g: Mor) -> Mor:
        def expand(x: Mor, y: Mor):
            return self.source.vcomposition(x, y)

        f = self
        return LazyComposition(f, g, expand)

class CategoryPrimMor(PrimMor, CategoryMor, metaclass=ABCMeta):
    """Models object `category.Mor` as primitive"""
    __slots__ = ()

class CategoryEq(Eq):
    """Models object `category.Eq`"""
    __slots__ = ()

    @override
    def sym(self):
        eq = Eq(self.starget, self.ssource)
        eq.proven = True
        return eq

    @override
    def trans(self, g: Eq):
        f = self
        # If `f` or `g` is ref, avoid creating new `Eq`.
        if f.ssource.same(f.starget):
            return g

        if g.ssource.same(g.starget):
            return f

        eq = Eq(g.ssource, f.starget)
        eq.proven = f.proven and g.proven
        return eq

    @override
    def compose_eq(self, e: Eq):
        d = self
        eq = Eq(
            d.ssource.compose(e.ssource),
            d.starget.compose(e.starget),
        )
        eq.proven = d.proven and e.proven
        return eq

class CategoryPrimEq(PrimEq, CategoryEq):
    """Models object `category.Eq` as primitive"""
    __slots__ = ()

class LazyComposition(CategoryMor):
    """Models lazy composition"""
    __slots__ = 'f', 'g', '_expanded', '_depth', '_expand'
    f: Mor
    g: Mor
    _expand: Callable[[Mor, Mor], Mor]
    _expanded: Mor
    _depth: int
    sameness_priority = True

    @property
    def depth(self):
        """Depth of composition"""
        return self._depth

    def __init__(self, f: Mor, g: Mor, expand: Callable[[Mor, Mor], Mor]):
        super().__init__(g.source, f.target)
        self.f = f
        self.g = g
        self._expand = expand
        self._depth = max(f.depth, g.depth) + 1

    def expanded(self):
        if hasattr(self, '_expanded'):
            return self._expanded

        self._expanded = self._expand(self.f, self.g)
        return self._expanded

    def ev(self, x: object):
        return self.expanded().ev(x)

    def hint(self):
        return self.expanded().hint()

    def same(self, x: Mor):
        if isinstance(x, type(self)):
            x = x.expanded()
        return self.expanded().same(x)

class Composition(CategoryMor):
    """Models the result of `category.compose`"""
    __slots__ = ('factors',)
    factors: tuple[Mor, ...]

    def __init__(self, source: Obj, target: Obj, factors: tuple[Mor, ...]):
        # Do not directly call class for instantiation, use `identity` or
        # `simplified` instead.
        super().__init__(source, target)
        self.factors = factors

    def split(self) -> tuple[Mor, Mor]:
        """Separate comoposition into the first factors and last factor"""
        if len(self.factors) <= 1:
            raise ValueError("Requires at least two factors")
        return self.simplified(self.factors[:-1]), self.factors[-1]

    @classmethod
    def simplified(cls, factors: Sequence[Mor]):
        """Creates composition after simplifying factors"""

        if not factors:
            raise ValueError("Requires at least one factor")

        _factors = cls.simplify(factors)

        if len(_factors) == 1:
            return _factors[0]

        return cls(factors[-1].source, factors[0].target, tuple(_factors))

    @classmethod
    def identity(cls, obj: Obj):
        """Creates identity"""
        return cls(obj, obj, ())

    @classmethod
    def simplify(cls, factors: Sequence[Mor]) -> Sequence[Mor]:
        """Simplifies factors"""
        _factors: list[Mor] = []
        for factor in factors:
            if isinstance(factor, LazyComposition):
                factor = factor.expanded()

            if isinstance(factor, Composition):
                _factors.extend(factor.factors)
            else:
                _factors.append(factor)
        return _factors

    def ev(self, x: object):
        res = x
        for factor in self.factors:
            res = factor.ev(res)

        return res

    def hint(self):
        return self.source, self.factors

    def same(self, x: Mor):
        return super().same(x) or (
            isinstance(x, Composition)
            and len(self.factors) == len(x.factors)
            and all(f.same(g) for f, g in zip(self.factors, x.factors))
            # This is required for comparing identities.
            and self.source.identical(x.source)
        )

    def __str__(self):
        name = super().__str__()
        if name is NotImplemented:
            return f'({'@'.join(str(factor) for factor in self.factors)})'
        return name

    def __repr__(self):
        return f'`comp {self!s}`'

CategoryObj.init_cls()
