"""Category cell classes"""
from typing import override
from abc import ABCMeta
from collections.abc import Sequence

from ..cells import Obj, PrimObj, Mor, PrimMor, Eq, PrimEq

class CategoryObj(Obj, metaclass=ABCMeta):
    """Models object `category.Obj`"""
    __slots__ = ()

    @override
    def identity(self):
        return Composition.identity(self)

class CategoryPrimObj(PrimObj, Obj):
    """Models object `category.Obj` as primitive"""
    __slots__ = ()

class CategoryMor(Mor, metaclass=ABCMeta):
    """Models object `category.Mor`"""
    __slots__ = ()

    @override
    def ref(self):
        return Eq(self, self)

    @override
    def compose(self, g: Mor) -> Mor:
        f = self
        return Composition.simplified(f, g)

class CategoryPrimMor(PrimMor, CategoryMor):
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

class Composition(CategoryMor):
    """Models the result of `category.compose`"""
    __slots__ = 'factors', '_defensive'
    factors: tuple[Mor, ...]

    @property
    def defensive(self) -> bool:
        """Some morphism in the composition is defensive."""
        return getattr(self, '_defensive', False)

    def __init__(
            self, source: Obj, target: Obj, factors: tuple[Mor, ...],
            defensive: bool = False,
        ):
        # Do not directly call class for instantiation, use `identity` or
        # `simplified` instead.
        super().__init__(source, target)
        self.factors = factors
        self._defensive = defensive

    @classmethod
    def simplified(cls, *factors: Mor):
        """Creates composition after simplifying factors"""

        if not factors:
            raise ValueError("Requires at least one factor")

        _factors = cls.simplify(factors)

        if len(_factors) == 1:
            return _factors[0]

        return cls(
            factors[-1].source, factors[0].target, tuple(_factors),
            defensive=any(f.defensive for f in _factors),
        )

    @classmethod
    def identity(cls, obj: Obj):
        """Creates identity"""
        return cls(obj, obj, ())

    @classmethod
    def simplify(cls, factors: tuple[Mor, ...]) -> Sequence[Mor]:
        """Simplifies factors"""
        _factors: list[Mor] = []
        for factor in factors:
            if isinstance(factor, Composition):
                _factors.extend(factor.factors)
            else:
                _factors.append(factor)
        return _factors

    def ev(self, x: object):
        res = x

        if self.defensive:
            res = self._defensive_enter(res)

            for factor in self.factors:
                if factor.defensive:
                    res.value = factor.ev(res)
                else:
                    res.value = factor.ev(res.value)

            res.exit()
            return res.value

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
