"""Lex cell classes"""
from abc import ABCMeta
from collections.abc import Iterable
from typing import Self, override
from itertools import chain

from ..cells import Obj, Mor, Eq, PrimEq
from .cart import (
    CartObj, CartMor, CartPrimMor, CartEq, CartComposition,
)

class LexObj(CartObj, metaclass=ABCMeta):
    __slots__ = ()

    @classmethod
    def init_cls(cls):
        cls._composition_cls = LexComposition

LexMor = CartMor
LexPrimMor = CartPrimMor

class LexEq(CartEq, metaclass=ABCMeta):
    """Models object `lex.Mor`"""
    __slots__ = ()

    @override
    def equalizer(self):
        source = self.ssource.source
        return Inclusion(Subobject(source, (self.ssignature(),)), source)

    @override
    def equalizer_pairing(self, mor: Mor):
        return EqualizerMor(mor, Subobject(mor.target, (self.ssignature(),)))

    @override
    def equalizer_pairing_unique(self, mor: Mor, fmor: Mor) -> Eq:
        eq = Eq(self.equalizer_pairing(fmor), mor)
        eq.proven = True
        return eq

class LexPrimEq(PrimEq, LexEq, metaclass=ABCMeta):
    """Models object `lex.Eq` as primitive"""
    __slots__ = ()

class Subobject(LexObj):
    __slots__ = '_sup', '_requirements'
    _sup: Obj
    _requirements: frozenset[tuple[Mor, Mor]]

    def conversion(self, obj: Obj):
        # Conversion applies even when the `self` is not a subobject of `obj`.
        # In this case lifting (through `restrict`) will be required, because
        # the resulting conversion will only have a superobjet of `obj` as
        # target.
        res = super().conversion(obj)

        # Create superobject of `obj` and `self`. This will be the target.
        reqs = self.requirements & obj.requirements
        if not reqs:
            sup = obj
        else:
            pass

        if res is None:
            try:
                return self.incl(obj)
            except ValueError:
                return None

        return res

    @property
    @override
    def sup(self):
        return self._sup

    @property
    @override
    def requirements(self):
        return self._requirements

    def __init__(self, sup: Obj, requirements: Iterable[tuple[Mor, Mor]]):
        # High-level does not only handle type checking, it also makes sure that
        # there are requirements and that the requirements are not tautologies
        # (proven equalities), so that the resulting subobject does not end up
        # being isomorphic to its superobject (which would be proven through the
        # universal property of the equalizer).

        if isinstance(sup, Subobject):
            self._sup = sup.sup
            requirements = chain(sup._requirements, requirements)
        else:
            self._sup = sup

        # The actual source of a requirement may end up being an intermediate
        # subobject of `self.sup`. One uses the largest source allowed by the
        # requirement. Type checking ensures that the source of the requirement
        # is an intermediate subobject.
        self._requirements = frozenset(requirements)
        if not self._requirements:
            # We allow this subobject to just be a copy of `sup` (the argument).
            raise ValueError("Can't create subobject without requirements")

    @override
    def incl(self, obj: Obj | None = None):
        # Strict inclusion
        if obj is None:
            obj = self.sup

        if (
            isinstance(obj, Subobject)
            and self.sup.identical(obj.sup)
            and self._requirements > obj.requirements
        ):
            return Inclusion(self, obj)

        raise ValueError("Not included")

    @override
    def fork(self, ssource: Mor, starget: Mor):
        if not (
            (ssource, starget) in self._requirements
            or (starget, ssource) in self._requirements
        ):
            raise ValueError("No proof from requirements")

        eq = Eq(ssource, starget).compose_eq(
            Inclusion(self, ssource.source).ref(),
        )
        eq.proven = True
        return eq

    def identical(self, x: Obj):
        return super().identical(x) or (
            isinstance(x, Subobject)
            and self.sup.identical(x.sup)
            and self._requirements == x.requirements
        )

    def hint(self):
        return self.sup, self._requirements

    def accepts(self, x: object):
        # That `x` is accepted by the source of `eq` is guaranteed by the order
        # of `self.requirements`.
        return self.sup.accepts(x) and all(
            # TODO: Eq.verify_ssignature(...)
            Eq(*eq).verify(x) for eq in self._requirements
        )

    def same(self, x: object, y: object):
        return self.sup.same(x, y)

    def proj(self, label: str | int) -> 'Mor':
        # The target of projections is never a subobject. This is fine, since
        # the needed object equalities are all registered, so that a lifting can
        # be done when needed.

        # If subobject is needed in requirement composition then the subobject
        # is recovered by the automatic restriction.
        return self.sup.proj(label)

# TODO: Use __new__ to handle case where initialization parameters actually require
# returning one of the parameters instead of a new instance. This applies for example
# in the case of product when only one component (without label is provided).
# TODO: Have "unpacking" LexProduct (unpacks subobject components)?
# TODO: An inclusion is like a projection, and therefore some comdiags have to be
# taken into account.
# TODO: Compare lifting of a morphism with lifting the composed morphism.

class Inclusion(CartMor):
    """Models inclusion"""
    # An inclusion where source and target are identical is at least
    # intensionally the same as the identity. Proving this however may not be
    # possible, since one does not allow subobjects without requirements.
    # It is then better to avoid creating identity inclusions, and in general
    # just create inclusions through the methods provided in this module, which
    # are guaranteed to produce valid inclusions.

    # An inclusion where source and target coincide is extensionally equal to
    # the identity. The high-level interface should keep this from happening.
    __slots__ = ()

    def incl_compose(self, mor: Self):
        """Compose with inclusion into a single inclusion"""
        return Inclusion(mor.source, self.target)

    def ev(self, x: object):
        return x

    def hint(self):
        return type(self), self.source, self.target

    def same(self, x: Mor):
        # This should not be interpreted as there only being one inclusion from
        # the object, but as there only being one with the given `ev`.
        return super().same(x) or (
            isinstance(x, Inclusion)
            and self.source.identical(x.source)
            and self.target.identical(x.target)
        )

class EqualizerMor(LexMor):
    """Models object corresponding to `lex.EqualizerMor`"""
    __slots__ = ('sup',)

    sup: Mor

    def after_incl(self, mor: 'Inclusion') -> Mor | tuple[Mor, Mor]:
        """Get supermorphism by composing with the inclusion"""
        target = mor.target
        sup = self.sup

        if sup.target.identical(target):
            return sup

        try:
            incl = sup.target.incl(target)
        except ValueError:
            # In this case `target` is supposed to be included in `sup.target`.
            _ = target.incl(sup.target)
            return EqualizerMor(sup, target)

        return incl, sup

    def __init__(self, mor: Mor, target: Obj):
        # Lift to `target`, which is a subobject of `mor.target`.
        # Type checking must make sure that the subobject condition holds
        # strictly, so that in particular the case where `mor.target` and
        # `target` are the same must be avoided (this would be extensionally
        # equal to `mor`).
        super().__init__(mor.source, target)
        self.sup = mor

    def ev(self, x: object):
        return self.sup.ev(x)

    def hint(self):
        return self.target, self.sup

    def same(self, x: Mor):
        return super().same(x) or (
            isinstance(x, EqualizerMor)
            and self.target.identical(x.target)
            and self.sup.same(x.sup)
        )

class LexComposition(CartComposition, LexMor):
    """Handles extra conditions that make two morphisms the same

    The extra condition is the one coming from composition of equalizer pairing
    and inclusion.
    """
    __slots__ = ()

    @classmethod
    def _simplify_proj_single_factor(
        cls, pmor: Mor, mor: Mor,
    ) -> Mor | tuple[Mor, Mor]:
        # TODO: The result of composing with an inclusion is always! the same morphism
        # but with a new more restricted source. We already do this when composing an
        # inclusion with an inclusion. Another case where we change the source of morphisms
        # is when readapting requirements during flattening (the sources are possibly partial
        # subobjects).

        # Projections are epi so they can't factor through inclusions.
        if isinstance(pmor, Inclusion):
            if isinstance(mor, Inclusion):
                return pmor.incl_compose(mor)

            if isinstance(mor, EqualizerMor):
                return mor.after_incl(pmor)

        # Composing an equalizer pairing gives another equalizer pairing by
        # composing the `sup` attribute of the original equalizer pairing. To be
        # consistent with the way we simplify pairings, we simplify towards the
        # latter form.
        if isinstance(mor, EqualizerMor):
            target = mor.target
            return EqualizerMor(pmor.compose(mor.sup), target)

        return super()._simplify_proj_single_factor(pmor, mor)

LexObj.init_cls()
