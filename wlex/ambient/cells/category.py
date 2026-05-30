"""Category cell classes"""
from typing import override, Callable
from abc import ABCMeta
from collections.abc import Sequence

from ..cells import (
    Obj, Mor, PrimMor, Eq, PrimEq, PrimEv, Axiom, TypeObj,
)

class CategoryObj(Obj, metaclass=ABCMeta):
    """Models object `category.Obj`"""
    __slots__ = ()

    _eq_cls: type[Eq]
    _composition_cls: type['Composition']

    @classmethod
    def init_cls(cls):
        cls._eq_cls = CategoryEq
        cls._composition_cls = Composition

    @classmethod
    def postulate(cls, ssource: Mor, starget: Mor):
        return cls._eq_cls(ssource, starget)

    @override
    def identity(self):
        return self._composition_cls.identity(self)

    @override
    @classmethod
    def vcomposition(cls, *factors: Mor) -> Mor:
        return cls._composition_cls.simplified(factors)

class CategoryTypeObj(TypeObj, CategoryObj):
    # This works because TypeObj implements abstract methods.
    __slots__ = ()

class CategoryMor(Mor, metaclass=ABCMeta):
    """Models object `category.Mor`"""
    __slots__ = ()

    @override
    def ref(self):
        eq = self.source.postulate(self, self)
        eq.proven = True
        return eq

    @override
    def compose(self, g: Mor) -> Mor:
        def expand(x: Mor, y: Mor):
            return self.source.vcomposition(x, y)

        f = self
        return LazyComposition(f, g, expand)

class CategoryPrimMor(PrimMor, CategoryMor):
    """Models object `category.Mor` as primitive"""
    __slots__ = ()

class CategoryPrimEv(PrimEv):
    __slots__ = ()

    def to_mor(self, source: Obj, target: Obj):
        return CategoryPrimMor(source, target, self.func)

class CategoryEq(Eq):
    """Models object `category.Eq`"""
    __slots__ = ()

    @override
    def sym(self):
        eq = self.ssource.source.postulate(self.starget, self.ssource)
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

        eq = self.ssource.source.postulate(g.ssource, f.starget)
        eq.proven = f.proven and g.proven
        return eq

    @override
    def compose_eq(self, e: Eq):
        d = self
        eq = self.ssource.source.postulate(
            d.ssource.compose(e.ssource),
            d.starget.compose(e.starget),
        )
        eq.proven = d.proven and e.proven
        return eq

class CategoryPrimEq(PrimEq, CategoryEq):
    """Models object `category.Eq` as primitive"""
    __slots__ = ()

class CategoryAxiom(Axiom):
    __slots__ = ()

    def to_eq(self, ssource: Mor, starget: Mor):
        return CategoryPrimEq(ssource, starget, self.public)

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

    def __repr__(self):
        return f'{type(self).__name__}({self.expanded()})'

class Composition(CategoryMor):
    """Models the result of `category.compose`"""
    __slots__ = ('factors',)
    factors: tuple[Mor, ...]

    def __init__(self, source: Obj, target: Obj, factors: tuple[Mor, ...]):
        # Do not directly call class for instantiation, use `identity` or
        # `simplified` instead.
        super().__init__(source, target)
        self.factors = factors

    def split(self):
        if len(self.factors) <= 1:
            raise ValueError("Requires at least two factors")

        return self.simplified(self.factors[:-1]), self.factors[-1]

    def drop_tail(self, tail_length: int = -1) -> Mor:
        if not self.factors:
            raise ValueError("Requires at least one factors")

        if tail_length < 0:
            return self.factors[-1]

        if tail_length == 0:
            return self

        if tail_length > len(self.factors):
            raise ValueError("`tail_length` can't be greater than `len(self.factors)`.")

        if tail_length == len(self.factors):
            return self.identity(self.source)

        return self.simplified(self.factors[tail_length:])

    def drop_head(self, head_length: int = -1) -> Mor:
        if not self.factors:
            raise ValueError("Requires at least one factors")

        if head_length < 0:
            return self.simplified(self.factors[:-1])

        if head_length == 0:
            return self

        if head_length > len(self.factors):
            raise ValueError("`head_length` can't be greater than `len(self.factors)`.")

        if head_length == len(self.factors):
            return self.identity(self.target)

        return self.simplified(self.factors[-head_length:])

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
        for factor in reversed(self.factors):
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

    def __repr__(self):
        name = self.name or ' @ '.join(repr(factor) for factor in self.factors)
        return f'{type(self).__name__}({name})'

CategoryObj.init_cls()
