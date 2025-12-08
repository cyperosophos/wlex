"""Lex cell classes"""
from typing import Self, override
from abc import ABCMeta
from collections.abc import Iterator, Sequence
from itertools import chain

from ..cells import Obj, Mor, Eq, PrimEq
from .cart import CartObj, CartMor, CartPrimMor, CartEq, CartComposition

# TODO: This method must be instead in a LexObj subclass in ambient.lex
# where Eq | None is the arg type, there is at least one equality
# (first, eqs) and the source of the equalities is the `obj` of the
# subobject.
# def requiring(self, *eqs: 'Eq') -> 'Obj':
#     """Create copy of object with requirements

#     A requirement is a public equality which is essential to the object, in
#     the sense that objects must have the same requirements in order to be
#     considered identical.
#     """
#     return Subobject(self, eqs)

LexObj = CartObj
LexMor = CartMor
LexPrimMor = CartPrimMor

class LexEq(CartEq, metaclass=ABCMeta):
    """Models morphism `lex.Mor`"""
    __slots__ = ()

    @override
    def equalizer(self):
        source = self.ssource.source
        return Inclusion(Subobject(
            source, (('', self),), flattened=False,
        ), source)

    @override
    def equalizer_pairing(self, mor: Mor):
        return EqualizerMor(mor, (('', self),), flattened=False)

    @override
    def equalizer_pairing_unique(self, mor: Mor, fmor: Mor) -> Eq:
        eq = Eq(self.equalizer_pairing(fmor), mor)
        eq.proven = True
        return eq

class LexPrimEq(PrimEq, LexEq, metaclass=ABCMeta):
    """Models object `lex.Eq` as primitive"""
    __slots__ = ()

LabeledParallel = tuple[str, Eq]

class Subobject(CartObj):
    """Models subobject

    A subobject is an object to which requirements have been associated.
    """
    __slots__ = '_sup', '_requirements', '_names'
    _sup: Obj
    _requirements: list[Eq]
    _names: dict[str, int]

    def __init__(
        self, obj: Obj, requirements: Sequence[LabeledParallel],
        flattened: bool = True,
    ):
        # The result is identical regardless of flattening.
        if not requirements:
            raise ValueError('No requirements for subobject')

        self._sup = obj
        self._requirements = [eq for _, eq in requirements]
        self._names = dict(
            (name, i) for i, (name, _) in enumerate(requirements) if name
        )

        if flattened and isinstance(obj, Subobject):
            # Just like in `name_to_len_idx`, only the first equality with
            # the name is the one that gets accessed by that name.
            reqs = list(self.all_requirements())
            names = dict(self.all_names())

            self._sup = self.sup
            self._requirements = reqs
            self._names = names

    @property
    def sup(self) -> Obj:
        """Superobject"""

        obj = self._sup
        if isinstance(obj, Subobject):
            return obj.sup

        return obj

    def labeled_requirements(self) -> list[LabeledParallel]:
        """Requirements with labels"""
        reqs = [('', r) for r in self.all_requirements()]

        for name, idx in self.all_names():
            reqs[idx] = (name, reqs[idx][1])

        return reqs

    def all_requirements(self) -> Iterator['Eq']:
        """Requirements including the one from the superobject"""
        obj = self._sup
        if isinstance(obj, Subobject):
            return chain(obj.all_requirements(), self._requirements)

        return iter(self._requirements)

    def requirements_length(self) -> int:
        """Length os all requirements"""
        obj = self._sup
        length = len(self._requirements)

        if isinstance(obj, Subobject):
            length += obj.requirements_length()

        return length

    def all_names(self) -> Iterator[tuple[str, int]]:
        """Names including the ones from the superobject"""
        obj = self._sup
        if isinstance(obj, Subobject):
            offset = obj.requirements_length()
            # In reverse order so that the first occurrence of a name masks all
            # subsequent occurrences. See `name_to_len_idx`.
            return chain(
                ((k, v + offset) for k, v in reversed(self._names.items())),
                obj.all_names(),
            )

        return iter(self._names.items())

    def name_to_len_idx(self, name: str) -> tuple[int, int]:
        """Name to length of all requirements and index"""
        obj = self._sup
        if isinstance(obj, Subobject):
            l, idx = obj.name_to_len_idx(name)
            length = l + len(self._requirements)

            if idx < 0:
                idx = self._names.get(name, -1)
                if idx >= 0:
                    idx += l

                return length, idx

            return length, idx

        return len(self._requirements), self._names.get(name, -1)

    def conversion(self, obj: Obj):
        return super().conversion(obj) or (
            self.included(obj) and Inclusion(self, obj)
        ) or None

    def included(self, x: Obj):
        """`x` includes `self`.

        This means that any value accepted by `self` is also accepted by `x`.
        """
        if super().identical(x):
            return True

        if isinstance(x, Subobject):
            return (
                self.sup.identical(x.sup)
                and set(self.all_requirements()) <= set(x.all_requirements())
            )

        return self.sup.identical(x)

    @override
    def req(self, name: str | int = 0):
        deep = isinstance(self._sup, Subobject)
        if deep:
            requirements = list(self.all_requirements())
        else:
            requirements = self._requirements

        if isinstance(name, int):
            idx = name
            if idx >= len(requirements) or idx < 0:
                raise ValueError("`name` of type `int` is out of range.")
        else:
            if deep:
                idx = self.name_to_len_idx(name)[1]
            else:
                idx = self._names.get(name, -1)

            if idx < 0:
                raise ValueError(
                    "`name` does not correspond to any requirement.",
                )

        eq = requirements[idx].compose_eq(Inclusion(self, self._sup).ref())
        eq.proven = True
        return eq

    def identical(self, x: Obj):
        return super().identical(x) or (
            isinstance(x, Subobject)
            and self.sup.identical(x.sup)
            and set(self.all_requirements()) == set(x.all_requirements())
        )

    def hint(self):
        return (
            type(self), self.sup, sum(hash(r) for r in self.all_requirements()),
        )

    def accepts(self, x: object):
        return self._sup.accepts(x) and all(
            eq.verify(x) for eq in self._requirements
        )

    def same(self, x: object, y: object):
        return self._sup.same(x, y)

class Inclusion(CartMor):
    """Models inclusion"""
    __slots__ = ()

    def incl_compose(self, mor: Self):
        """Compose with inclusion into a single inclusion"""
        return Inclusion(mor.source, self.target)

    def ev(self, x: object):
        return x

    def hint(self):
        return type(self), self.source, self.target

    def same(self, x: Mor):
        return super().same(x) or (
            isinstance(x, Inclusion)
            and self.source.identical(x.source)
            and self.target.identical(x.target)
        )

class EqualizerMor(LexMor):
    """Models object corresponding to `lex.EqualizerMor`"""
    __slots__ = ('_sup',)
    # The shape of the actual limit is more like a flower,
    # each petal being a parallel pair.
    # So the components are the petals, i.e. equalities.
    # See `p(c(p_, pt), Mor).where(th.req(1))`  in theory/cart.py
    # `where` has to be a method of `Mor` that modifies the morphism
    # (fork morphism) by lifting it to the equalizer.
    # The equality passed through `where` contains the fork morphism
    # as common (right) factor of the equality signature.
    # In this case the ssource and starget have to be rewritten from
    # `(c(target, Mor), c(source, p_, pt))` to
    # `(c(target, $1, p(c(p_, pt), Mor)), c(source, $0, p(c(p_, pt), Mor)))`
    # Inferring this is probably not simple, so one must always provide the
    # parallel pair corresponding to the equality.
    # TODO: Should the pairing for the composition mentioned here have names
    # f and g? Probably not since e.g. args in python don't have to be named.
    # Check Product methods accepts, same, identical, etc.
    _sup: Mor

    def after_incl(self, mor: 'Inclusion') -> Mor:
        """Get supermorphism by composing with the inclusion"""
        target = mor.target

        if isinstance(target, Subobject):
            return EqualizerMor(self.sup, target.labeled_requirements())

        return self.sup

    def __init__(
        self, mor: Mor, requirements: Sequence[LabeledParallel],
        flattened: bool = True,
    ):
        # When instantiating `ProductMor`, we may provide a `consistency`
        # argument. In contrast, here we never provide the equalities that prove
        # the parallel pairs, because unlike checking consistency checking the
        # forks is part of the theory. For this we use the binary operation
        # `equalizer_pairing`.
        target = Subobject(mor.target, requirements, flattened=flattened)
        super().__init__(mor.source, target)

        self._sup = mor
        if flattened and isinstance(mor, EqualizerMor):
            self._sup = self.sup

    @property
    def sup(self) -> Mor:
        """Superobject"""
        mor = self._sup
        if isinstance(mor, EqualizerMor):
            return mor.sup

        return mor

    def ev(self, x: object):
        return self._sup.ev(x)

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
            assert isinstance(target, Subobject)
            return EqualizerMor(pmor.compose(mor.sup), target.labeled_requirements())

        return super()._simplify_proj_single_factor(pmor, mor)

LexMor.comp_cls = LexComposition
