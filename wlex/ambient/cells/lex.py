"""Lex cell classes"""
from abc import ABCMeta
from collections.abc import Collection, Callable, Iterable, Sequence
from typing import Self, override
from itertools import chain

from ..cells import Obj, Mor, Eq, PrimEq, TypeObj, Axiom
from .cart import (
    CartObj, CartMor, CartPrimMor, CartEq, CartComposition,
)

class LexObj(CartObj, metaclass=ABCMeta):
    __slots__ = ()

    @classmethod
    def init_cls(cls):
        cls._eq_cls = LexEq
        cls._composition_cls = LexComposition
        cls._subobject_cls = Subobject
        cls._equalizer_mor_cls = EqualizerMor

    def subobject(self, requirements: Collection[tuple[Mor, Mor]]):
        # There still has to be a `requiring` method that does type-checking
        # at the context level.
        if len(requirements) == 0:
            return self

        return self._subobject_cls(self, requirements)

    @override
    def incl_join(self, obj: Obj) -> Obj:
        if not self.sup.identical(obj.sup):
            raise ValueError('Must share superobject')

        shared = self.requirements & obj.requirements
        return self.sup.subobject(shared)

class LexTypeObj(TypeObj, LexObj):
    __slots__ = ()

LexMor = CartMor
LexPrimMor = CartPrimMor

class LexEq(CartEq, metaclass=ABCMeta):
    """Models object `lex.Mor`"""
    __slots__ = ()

    @staticmethod
    def _lazy_subobject_expand(sup: Obj, req: tuple[Mor, Mor]):
        return sup.subobject((req,))

    @override
    def equalizer(self):
        source = self.ssource.source
        # There is no point in this being lazy since we'll need the fork,
        # and the fork is an equality for which we'll need to call
        # `identical` when composing, etc.
        return Inclusion(
            source.subobject((self.ssignature(),)),
            source,
        )

    @override
    def equalizer_pairing(self, mor: Mor):
        return LazySubobject(
            mor.target, self.ssignature(),
            self._lazy_subobject_expand,
        ).lift(mor)

    @override
    def equalizer_pairing_unique(self, mor: Mor, fmor: Mor) -> Eq:
        eq = self.ssource.source.postulate(self.equalizer_pairing(fmor), mor)
        eq.proven = True
        return eq

class LexPrimEq(PrimEq, LexEq):
    """Models object `lex.Eq` as primitive"""
    __slots__ = ()

class LexAxiom(Axiom):
    __slots__ = ()

    def to_eq(self, ssource: Mor, starget: Mor):
        return LexPrimEq(ssource, starget, self.public)

class LiftingObj(LexObj, metaclass=ABCMeta):
    __slots__ = ('_sup',)
    _sup: Obj

    @override
    def lift(self, mor: 'Mor'):
        # This is also used for LazySubobject since a lazy EqualizerMor is just
        # an EqualizerMor with a lazy target.
        if self.identical(mor.target):
            return mor

        return self._equalizer_mor_cls(mor, self)

class LazySubobject(LiftingObj):
    __slots__ = '_requirement', '_expanded', '_expand'
    _requirement: tuple[Mor, Mor]
    _expand: Callable[[Obj, tuple[Mor, Mor]], Obj]
    _expanded: Obj
    identity_priority = True

    def __repr__(self):
        return f'{type(self).__name__}({self.expanded()})'

    def __init__(
        self, sup: Obj,
        requirement: tuple[Mor, Mor],
        expand: Callable[[Obj, tuple[Mor, Mor]], Obj],
    ):
        super().__init__()
        self._sup = sup
        self._requirement = requirement
        self._expand = expand

    def expanded(self):
        if hasattr(self, '_expended'):
            return self._expanded

        self._expanded = self._expand(self._sup, self._requirement)
        return self._expanded

    def trim(self, obj: Obj):
        return self.expanded().trim(obj)

    @property
    @override
    def sup(self):
        return self.expanded().sup

    @property
    @override
    def requirements(self):
        return self.expanded().requirements

    @override
    def incl(self, obj: Obj | None = None):
        return self.expanded().incl(obj=obj)

    @override
    def fork(self, ssource: Mor, starget: Mor):
        return self.expanded().fork(ssource, starget)

    def identical(self, x: Obj):
        if isinstance(x, type(self)):
            x = x.expanded()

        return self.expanded().identical(x)

    def hint(self):
        return self.expanded().hint()

    def accepts(self, x: object):
        return self.expanded().accepts(x)

    def same(self, x: object, y: object):
        return self.expanded().same(x, y)

    def proj(self, label: str | int) -> Mor:
        return self.expanded().proj(label)

    def iso_relabeling(self, relabeling: Iterable[tuple[str | int, str | int]]):
        return self.expanded().iso_relabeling(relabeling)

    def sequence_relabeling(self, relabeling: Sequence[str | int]):
        return self.expanded().sequence_relabeling(relabeling)

    def with_labels(self, relabeling: Iterable[tuple[str | int, str | int]]):
        return self.expanded().with_labels(relabeling)

    def relabel(
        self, relabeling: Iterable[tuple[str | int, str | int]],
    ):
        return self.expanded().relabel(relabeling)

    @override
    def trim_join(self, obj: Obj):
        return self.expanded().trim_join(obj)

    @override
    def incl_join(self, obj: Obj):
        return self.expanded().incl_join(obj)

class Subobject(LiftingObj):
    __slots__ = ('_requirements',)
    _requirements: frozenset[tuple[Mor, Mor]]

    def __repr__(self):
        reqs = ', '.join(f'{x} = {y}' for x, y in self._requirements)
        name = self.name or f'{self.sup} | {reqs}'

        return f'{type(self).__name__}({name})'

    @override
    def trim_join(self, obj: Obj):
        return self.sup.trim_join(obj)

    def iso_relabeling(self, relabeling: Iterable[tuple[str | int, str | int]]):
        return self.sup.iso_relabeling(relabeling)

    def sequence_relabeling(self, relabeling: Sequence[str | int]):
        return self.sup.sequence_relabeling(relabeling)

    def with_labels(self, relabeling: Iterable[tuple[str | int, str | int]]):
        return self.sup.with_labels(relabeling)

    def relabel(
        self, relabeling: Iterable[tuple[str | int, str | int]],
    ):
        return self.sup.relabel(relabeling)

    def trim(self, obj: Obj):
        # TODO: Preserve requirements?
        if self.identical(obj):
            return self.identity()

        return self.sup.trim(obj.sup)

    @property
    @override
    def sup(self):
        return self._sup

    @property
    @override
    def requirements(self):
        return self._requirements

    def __new__(cls, sup: Obj, requirements: Collection[tuple[Mor, Mor]]):
        if len(requirements) == 0:
            if isinstance(sup, Subobject):
                return sup

        return super().__new__(cls)

    def __init__(self, sup: Obj, requirements: Collection[tuple[Mor, Mor]]):
        super().__init__()
        # High-level does not only handle type checking, it also makes sure that
        # there are requirements and that the requirements are not tautologies
        # (proven equalities), so that the resulting subobject does not end up
        # being isomorphic to its superobject (which would be proven through the
        # universal property of the equalizer).

        # Subobject with the same requirements up to symmetry (of equality) are
        # only isomorphic.

        if isinstance(sup, Subobject):
            if len(requirements) == 0:
                return

            self._sup = sup.sup
            self._requirements = frozenset(
                chain(sup._requirements, requirements),
            )
        else:
            assert requirements
            self._sup = sup
            self._requirements = frozenset(requirements)

        # The actual source of a requirement may end up being an intermediate
        # subobject of `self.sup`. One uses the largest source allowed by the
        # requirement. Type checking ensures that the source of the requirement
        # is an intermediate subobject.
        self._requirements = frozenset(requirements)

    @override
    def incl(self, obj: Obj | None = None):
        if obj is None:
            # Strict inclusion
            obj = self.sup
        elif self.identical(obj):
            return self.identity()

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

        eq = self.postulate(ssource, starget).compose_eq(
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
            # TODO: Eq.verify_ssignature(...) ?
            self.postulate(*eq).verify(x) for eq in self._requirements
        )

    def same(self, x: object, y: object):
        return self.sup.same(x, y)

    def proj(self, label: str | int) -> Mor:
        # The target of projections is never a subobject. This is fine, since
        # the needed object equalities are all registered, so that a lifting can
        # be done when needed.

        # If subobject is needed in requirement composition then the subobject
        # is recovered by the automatic restriction.
        return self.sup.proj(label)

# TODO: Use __new__ to handle case where initialization parameters actually require
# returning one of the parameters instead of a new instance. This applies for example
# in the case of product when only one component (without label is provided).
# Actually handle this in methods like vproduct (unless the same type is created), etc. and make sure that direct instantiation
# is not being used.
# TODO: Have "unpacking" LexProduct (unpacks subobject components)?
# TODO: -> An inclusion is like a projection, and therefore some comdiags have to be
# taken into account.
# TODO: -> Compare lifting of a morphism with lifting the composed morphism.
# This is specially important in the case of considering the process of restricting
# previous factors in the composition. Should one restrict the whole composition of the
# previous factors? Or just the previous factor? The first option seems simpler but it
# may miss tautologies. One must then try splitting in order to find the tautologies.
# Either way the process somehow seems to end being quadratic.

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

    def __repr__(self):
        name = self.name or f'{self.source} -> {self.target}'

        return f'{type(self).__name__}({name})'

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

    # `exfit` would have to change both `sup` (therefore `source`) and `target`
    # (by exfitting requirements). Therefore we don't modify the inherited
    # exfit and instead provide a context level exfit that handles the new
    # requirements.

    def __repr__(self):
        name = self.name or f'{self.sup}: {self.target}'

        return f'{type(self).__name__}({name})'

    def after_incl(self, mor: Inclusion) -> tuple[Mor, Mor]:
        """Get supermorphism by composing with the inclusion"""
        target = mor.target
        sup = self.sup

        try:
            # Case where new target is larger than `sup.target`
            incl = sup.target.incl(target)
        except ValueError: # TODO: Use specific error!!
            # In this case `target` is supposed to be included in `sup.target`.
            # Following the analogy with `after_proj`, this more or less
            # corresponds to the case where the whole projection is consumed.
            # One can consider this case as overlapping with the other when
            # `incl` is the identity.

            # We don't check that `mor.source` is identical to `self.target`,
            # because that's the task of type-checking, which also guarantees
            # that `target` is a superobject of `self.target`, so that all
            # forks required by `target` are also required by `self.target`,
            # which means that the necessary type-checking for lifting would
            # be passed.

            # If `target` is not included in `sup.target`, then we get the
            # intersection, so that the return value has an inclusion that gets
            # rid of the extra requirements of `sup.target`.
            t = sup.target.subobject(target.requirements)

            # Here the inclusion ends up just being the identity when `target`
            # is included in `sup.target`.
            return t.incl(target), EqualizerMor(sup, t)

        # In this case `sup.target` is the source of the inclusion, so `sup`
        # doesn't get lifted.
        return incl, sup

    def __init__(self, mor: Mor, target: Obj):
        # Lift to `target`, which is a subobject of `mor.target`.
        # Type checking must make sure that the subobject condition holds
        # strictly, so that in particular the case where `mor.target` and
        # `target` are the same must be avoided (this would be extensionally
        # equal to `mor`).
        super().__init__(mor.source, target)

        if isinstance(mor, EqualizerMor):
            self.sup = mor.sup
        else:
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
        # TODO: The result of precomposing with an inclusion is always! the same morphism
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
        # latter form. This is also compatible to how we lift when restricting,
        # because we lift the whole preceding composition instead of just the
        # single preceding factor (which due to the precomposition with an
        # inclusion for the restriction would require repeating the process for
        # each of the previous factors until reaching the source or until all
        # requirements get discarded as tautologies).
        if isinstance(mor, EqualizerMor):
            return EqualizerMor(pmor.compose(mor.sup), mor.target)

        return super()._simplify_proj_single_factor(pmor, mor)

LexObj.init_cls()
