"""Category cell classes"""
from typing import override, overload
from itertools import chain
from abc import ABCMeta

from ..cells import Obj, PrimObj, Mor, PrimMor, Eq, PrimEq

class CategoryObj(Obj, metaclass=ABCMeta):
    """Models object `category.Obj`"""
    __slots__ = ()

    @override
    def identity(self):
        return Composition(self)

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
        if isinstance(g, Composition) and not g.factors:
            return f
        return Composition(f, g)

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

    @override
    def compose(self, g: Mor):
        if not self.factors:
            return g
        return super().compose(g)

    @overload
    def __init__(self, target: Obj) -> None: ...
    @overload
    def __init__(self, *factors: Mor) -> None: ...
    def __init__(self, target: Obj | Mor, *factors: Mor):
        if isinstance(target, Obj):
            if factors:
                raise ValueError(
                    "Can't provide `factors` along with `source`. Composition"
                    "must be identity",
                )
            super().__init__(target, target)
            self.factors = ()
            return

        if not factors:
            raise ValueError("Single factor not allowed")

        first = target
        factor_it = chain((first,), factors)
        super().__init__(factors[-1].source, first.target)
        _factors: list[Mor] = []
        for factor in factor_it:
            if isinstance(factor, Composition):
                _factors.extend(factor.factors)
            else:
                _factors.append(factor)

        if len(_factors) == 1:
            # Identity stripping must occur before instantiation.
            raise ValueError

        self.factors = tuple(_factors)
        self._defensive = any(f.defensive for f in _factors)

    def ev(self, x: object):
        res = x

        if self.defensive:
            res = self._as_defensive(res)

            for factor in self.factors:
                if factor.defensive:
                    res.value = factor.ev(res)
                else:
                    res.value = factor.ev(res.value)

            res.stack.pop()
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
        return f'({'@'.join(str(factor) for factor in self.factors)})'

    def __repr__(self):
        return f'`comp {self!s}`'
