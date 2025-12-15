"""Lex cell classes"""
from typing import Self, override
from abc import ABCMeta
from collections.abc import Iterable, Iterator, Sequence
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
    """Models object `lex.Mor`"""
    __slots__ = ()

    @override
    def equalizer(self):
        source = self.ssource.source
        return Inclusion(Equalizer(source, self), source)

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

class Equalizer(CartObj):
    """Minimal model of equalizer"""
    __slots__ = 'sup', 'requirement'
    sup: Obj
    requirement: Eq

    def __init__(self, sup: Obj, requirement: Eq):
        self.sup = sup
        self.requirement = requirement

    def accepts(self, x: object) -> bool:
        return self.sup.accepts(x) and self.requirement.verify(x)

    def same(self, x: object, y: object) -> bool:
        return self.sup.same(x, y)

    def to_partial_subobject(self, name: str):
        """Convert to subobject"""
        return PartialSubobject(self.sup, name, self.requirement)

class BaseSubobject:
    __slots__ = ()
    sup: Obj
    requirements: list[Eq]
    names: dict[str, int]

    def labeled_requirements(self) -> list[LabeledParallel]:
        """Requirements with labels"""
        reqs = [('', r) for r in self.requirements]

        for name, idx in self.names.items():
            reqs[idx] = (name, reqs[idx][1])

        return reqs


class Subobject(CartObj, BaseSubobject):
    """Models subobject

    A subobject is an object to which requirements have been associated.
    """
    __slots__ = 'sup', 'requirements', 'names'

    def __init__(self, sup: Obj, requirements: Sequence[LabeledParallel]):
        if not requirements:
            raise ValueError('No requirements for subobject')

        if isinstance(sup, (Subobject, PartialSubobject)):
            raise TypeError('Subobject is not allow as superobject.')

        self.sup = sup
        self.requirements = [eq for _, eq in requirements]
        self.names = dict(
            (name, i) for i, (name, _) in enumerate(requirements) if name
        )

    def conversion(self, obj: Obj):
        return super().conversion(obj) or (
            self.included(obj) and Inclusion(self, obj)
        ) or None

    def included(self, x: Obj):
        """`x` includes `self`.

        This means that any value accepted by `self` is also accepted by `x`.
        """
        # To make sense of inclusion for purpose of conversion, names also must
        # coincide. In doesn't make sense to allow conversion when names don't
        # coincide, because the effect of laws is different. Laws that work on
        # the superobject must work the same way on the subobject?
        # In the case of products names that appear in the source of the conversion
        # must appear in the target of the conversion. The analogous design for
        # subobject and superobjects means that names of subobject requirements
        # which appear in superobject must correspond to the same indices.
        # Transformations that work on the losely named product must work the same
        # way on the product. Requirements cannot be reordered like the components
        # of a product, they are only accessed through laws and transformations built
        # with `where`. Inclusions with consistent naming must be explicitly built,
        # just like inclusions where the order of requirements is different.
        # Consistent naming ensures that the result is the same in the case of refactoring
        # by composing directly a morphism with the law (in which case no inclusion
        # would be involved), and if the result cannot be the same then an early failure
        # occurs. More flexibility is allowed by the fact that names don't reorder
        # requirements (like component names in product). If a name shows up in the
        # subobject and in the superobject then it must refer to the same equality.
        # A name can show up in the subobject but not in the superobject.
        if super().identical(x):
            return True

        sup = self.sup
        if isinstance(x, Subobject) and sup.identical(x.sup):
            reqs = self.requirements
            xreqs = x.requirements
            names = self.names
            xnames = x.names

            if len(reqs) < len(xreqs):
                return False

            for r, s in zip(reqs, xreqs):
                if not r.parallel(s):
                    return False

            for name, idx in xnames.items():
                if name in names and names[name] != idx:
                    return False

            return True

        return sup.identical(x)

    @override
    def req(self, name: str | int = 0):

        deep = isinstance(self.sup, Subobject)
        if deep:
            requirements = list(self.all_requirements())
        else:
            requirements = self.requirements

        if isinstance(name, int):
            idx = name
            if idx >= len(requirements) or idx < 0:
                raise ValueError("`name` of type `int` is out of range.")
        else:
            if deep:
                idx = self.name_to_len_idx(name)[1]
            else:
                idx = self.names.get(name, -1)

            if idx < 0:
                raise ValueError(
                    "`name` does not correspond to any requirement.",
                )

        # TODO: target of inclusion must be partial object
        # Just directly use the source of the requirement. While the composition does
        # not undergo any check of source matching target, it is better to follow the
        # consistently.
        eq = requirements[idx].compose_eq(Inclusion(self, self.sup).ref())
        eq.proven = True
        return eq

    def identical(self, x: Obj):
        return super().identical(x) or (
            isinstance(x, Subobject)
            and self.top_sup.identical(x.top_sup)
            and set(self.all_requirements()) == set(x.all_requirements())
        )

    def hint(self):
        return (
            type(self), self.top_sup, sum(hash(r) for r in self.all_requirements()),
        )

    def accepts(self, x: object):
        return self.sup.accepts(x) and all(
            eq.verify(x) for eq in self.requirements
        )

    def same(self, x: object, y: object):
        return self.sup.same(x, y)

class PartialSubobject(CartObj):
    __slots__ = 'sup', 'requirements', 'names', 'req_length'
    sup: Obj
    requirements: list[Eq]
    names: dict[str, int]
    req_length: int

    def __init__(self, sup: Obj, name: str, requirement: Eq):
        if isinstance(sup, PartialSubobject):
            requirements = sup.requirements
            names = sup.names
            if sup.req_length < len(requirements):
                raise ValueError("Can't reuse partial subobject as superobject")

            self.sup = sup.sup
            self.requirements = requirements
            self.names = names

            if name:
                # `name` masks any previous occurrence of the same key.
                names[name] = len(requirements)

            requirements.append(requirement)
            self.req_length = len(requirements)
        else:
            self.sup = sup
            self.requirements = [requirement]

            if name:
                self.names = {name: 0}
            else:
                self.names = {}

            self.req_length = 1

    # TODO: The superobject can be a product, with some components themselves having
    # requirements. These requirements must become part of the subobject requirements.

    # TODO: Proofs in `where` are equalities, so when using laws one must explicitly
    # compose with the source in order to get the equality. One writes
    # `req() @ X` or `t(req(0), req(1)) @ X` where X is the subobject.
    # This solution appears then to be to disallow requirements that depend on requirements
    # in the same `where` call. No partial subobjects, no flattening!
    # Some `where` calls would then become two `where` calls.
    # The source of the equalizer_mor has to be the source of the proofs, this
    # points to not needing to explicitly compose with `X`. Avoid as well explicit
    # composition with inclusion? Unless there is a single requirement,
    # req(...) must give an inclusion (besides the one that gets composed with the requirement).
    # This inclusion goes from the superobject to the largest admissible source.
    # !! The goal is to prove that two equalizer morphisms are the same
    # even if they differ only by the inclusion factor. This should be possible
    # intentionally by using the equalizer_pairing_unique.

    # TODO: Implement hint and identical! One still needs equality `parallel`
    # to work when using reqs. f @ i and g @ i are the same when they only differ
    # by the requirements of the source of the first factor. This is the nature
    # of (intensional) inclusions (which include coprojections). Notice that in the case of
    # coprojections extensivity seems to be what allows overloading.
    # Think of constructing an isomorphism of subobjects with the same requirements
    # in different order. The sources of the requirements will end up being different
    # due to the order. A requirement that appears later in the list will itself have
    # more (superfluous) requirements. This is comparable to the situation where not all
    # components of the superobject product are used. In this case the transformation ends up
    # giving a composition whose last factor is a projection.
    # The arguments of `where` are requirements along with their proofs.
    # In a sense laws allow deferring the proof. Define f, g: X -> Y and h: Z -> X.
    # Suppose e: f @ h == g @ h. One gets h': Z -> X' where X' has requirement f == g.
    # h' is h with requirement f == g and proof e. The proof must be parallel to the
    # composition of the requirement with h. (Perhaps rename req to proof.)
    # The requirement in `where` can be a law (but concerned with the proof being a law). When setting the source to the partial
    # subobject this law becomes an (unproven) equality, which turns the target of the morphism
    # into a subobject. Just like composition with transformation projections results in composition with projections,
    # the result of `where` with a law must be a composition with an inclusion.
    # The morphism composed with the inclusion must have the largest admissible source.
    # When a proof in `where` is a law, the resulting morphism is a transformation.
    # So one deduces this largest source from the laws used in the proofs?

    @override
    def req(self, name: str | int = 0):
        # Raises IndexError when `name` is an index out of range
        sup = self.sup
        if isinstance(name, str):
            idx = self.names.get(name)

            if idx is None:
                if isinstance(sup, Subobject):
                    return sup.req(name)

                raise ValueError(
                    "`name` does not correspond to any requirement"
                )
        else:
            idx = name
            if isinstance(sup, Subobject):
                sup_reqs = sup.requirements
                sup_len = len(sup_reqs)

                if idx < sup_len:
                    return sup.req(idx)

                idx -= sup_len

        eq = self.requirements[idx].compose_eq(
            Inclusion(self, self.sup).ref(),
        )
        eq.proven = True
        return eq

    def labeled_requirements(self):
        sup = self.sup
        if isinstance(sup, Subobject):
            yield from sup.labeled_requirements()



    def to_subobject(self):
        if self.req_length < len(self.requirements):
            raise ValueError(
                "Can't convert partial subobject to subobject after using as "
                "superobject"
            )

        sup = self.sup
        if isinstance(sup, Subobject):
            requirements = chain(
                sup.labeled_requirements(), self.labeled_requirements(),
            )







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
    # Inferring this is probably not simple!!, so one must always provide the
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
            assert isinstance(target, Subobject)
            return EqualizerMor(pmor.compose(mor.sup), target.labeled_requirements())

        return super()._simplify_proj_single_factor(pmor, mor)

LexMor.comp_cls = LexComposition
