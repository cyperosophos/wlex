"""Category cell classes"""
from typing import override
from abc import ABCMeta
from collections.abc import Sequence

from ..cells import Obj, Mor, PrimMor, Eq, PrimEq

class CategoryObj(Obj, metaclass=ABCMeta):
    """Models object `category.Obj`"""
    __slots__ = ()

    @override
    def identity(self):
        return Composition.identity(self)

class CategoryMor(Mor, metaclass=ABCMeta):
    """Models object `category.Mor`"""
    __slots__ = ()

    @override
    def ref(self):
        return Eq(self, self)

    @override
    def compose(self, g: Mor) -> Mor:
        f = self
        return LazyComposition(f, g)

class CategoryPrimMor(PrimMor, CategoryMor, metaclass=ABCMeta):
    """Models object `category.Mor` as primitive"""
    __slots__ = ()

class CategoryEq(Eq):
    """Models object `category.Eq`"""
    __slots__ = ()

    @override
    def sym(self):
        return Eq(self.starget, self.ssource)

    @override
    def trans(self, g: Eq):
        f = self
        # If `f` or `g` is ref, avoid creating new `Eq`.
        if f.ssource.same(f.starget):
            return g

        if g.ssource.same(g.starget):
            return f

        return Eq(g.ssource, f.starget)

    @override
    def compose_eq(self, e: Eq):
        d = self
        return Eq(
            d.ssource.compose(e.ssource),
            d.starget.compose(e.starget),
        )

class CategoryPrimEq(PrimEq, CategoryEq):
    """Models object `category.Eq` as primitive"""
    __slots__ = ()

class LazyComposition(CategoryMor):
    """Models lazy composition"""
    __slots__ = 'f', 'g', '_expanded'
    f: Mor
    g: Mor
    _expanded: Mor
    sameness_priority = True

    def __init__(self, f: Mor, g: Mor):
        super().__init__(g.source, f.target)
        self.f = f
        self.g = g

    def expanded(self):
        """Underlying composition"""
        if hasattr(self, '_expanded'):
            return self._expanded

        self._expanded = Composition.simplified(self.f, self.g)
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

    @classmethod
    def simplified(cls, *factors: Mor):
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
    def simplify(cls, factors: tuple[Mor, ...]) -> Sequence[Mor]:
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
