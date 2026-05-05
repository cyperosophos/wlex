"""Lex cell classes"""
from typing import Self, override
from abc import ABCMeta
from collections.abc import Iterable, Sequence
from bisect import bisect_left as bisect

from ..cells import Obj, Mor, Eq, PrimEq
from .cart import (
    CartObj, CartMor, CartPrimMor, CartEq, CartComposition, Product, LabeledObj,
)

# TODO: Lifting a pairing (converting its target to a product subobject)
# should be currently supported, since the fork with the projection inserted
# in the parallel pair is extensionally equal to the original fork. Check that this is the case!

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

class LexObj(CartObj, metaclass=ABCMeta):
    __slots__ = ()

    # TODO: Does this need _subobject_cls, etc.?

    @classmethod
    def init_cls(cls):
        cls._composition_cls = LexComposition
        cls._product_cls = LexProduct

LexMor = CartMor
LexPrimMor = CartPrimMor

class LexEq(CartEq, metaclass=ABCMeta):
    """Models object `lex.Mor`"""
    __slots__ = ()

    @override
    def equalizer(self):
        source = self.ssource.source
        return Inclusion(Subobject(source, (('', self),)), source)

    @override
    def equalizer_pairing(self, mor: Mor):
        return EqualizerMor(mor, Subobject(mor.target, (('', self),)))

    @override
    def equalizer_pairing_unique(self, mor: Mor, fmor: Mor) -> Eq:
        eq = Eq(self.equalizer_pairing(fmor), mor)
        eq.proven = True
        return eq

class LexPrimEq(PrimEq, LexEq, metaclass=ABCMeta):
    """Models object `lex.Eq` as primitive"""
    __slots__ = ()

LabeledParallel = tuple[str, Eq]

class BaseSubobject2(LexObj):
    __slots__ = ()
    sup: Obj
    requirements: list[Eq]
    named_requirements: dict[str, Eq]

class Subobject(LexObj):
    __slots__ = '_sup', 'requirements', 'named_requirements'
    _sup: Obj
    requirements: list[Eq]
    named_requirements: dict[str, tuple[int, Eq]]

    def conversion(self, obj: Obj):
        return super().conversion(obj) or (
            self.diff(obj) > 0 and Inclusion(self, obj)
        ) or None

    @property
    @override
    def sup(self):
        return self._sup

    @override
    def labeled_requirements(self):
        res = [('', req) for req in self.requirements]
        for label, (idx, req) in self.named_requirements.items():
            res[idx] = (label, req)

        return res

    def __init__(self, sup: Obj, requirements: Iterable[LabeledParallel]):
        # When requirements are provided in the high-level interface, their
        # protypical source (source of the last factor) is the top superobject.
        # High-level composition then restricts this source (if there are no
        # fork proofs for requirements of previous factors). Type checking
        # (through binary `equalizer`) requires that the requirement be again
        # precomposed with an appropriate (general and obtained through lifting)
        # inclusion if needed. However, this precomposition is not included in
        # the requirements of variadic instantiation, because that would ruin
        # normalization. Since the forks generated from the equality will always
        # have the bottom subobject as their source, one should always be able
        # to get the proofs from the requirements of another subobject even if
        # their sources were restricted in a different way. This mean that one
        # would be able to prove that the two subobjects are isomorphic even if
        # not identical. At the high-level, it may then seem helpful to disallow
        # requirements whose source is a subobject, but this would be a problem
        # as the restriction to a subobject may already be part of the
        # signature of the last factor.

        # Notice that empty requirements is allowed (although useless).
        if isinstance(sup, Subobject):
            self._sup = sup.sup
            nreqs = sup.named_requirements.copy()
            reqs = sup.requirements[:]
        else:
            self._sup = sup
            nreqs: dict[str, tuple[int, Eq]] = {}
            reqs: list[Eq] = []

        for name, req in requirements:
            # TODO: The source of `req` is `sup` not `self.sup`.
            # The source of `req` as provided in parameters is already `sup`.
            # The fork is the `req` composed with the inclusion from `self`
            # to the source of the `req` (`self.sup` or a subobject thereof
            # such as `sup`). This inclusion is guaranteed to exist.
            # The high-level takes care of making sure that the source of `req`
            # is `sup` (type checking). This isn't enough, since the result for
            # purposes of `identical` comparison ends up being the same as always
            # making `self.sup` be `sup`, which is not aggressive normalization.
            # One may leave the source of `req` unchanged for the sake of simplicity,
            # instead of enlarging it to become the largest admissible subobject of `self.sup`.
            # One must then allow the source of `req` to be a superobject of `sup` instead of `sup`.
            # An example is a requirement with compose @ ($f, $g). The lifting occurs
            # through a requirement of the superobject (itself a subobject).
            # In this case $f and $g are transformations, but if they were actual morphisms
            # then precomposing with an inclusion would be required. For type checking
            # of the binary equalizer_pairing the source must be the `sup` (but it can also be a subobject by making all prev reqs hold).
            # There must actually be a way to extend the source of `req` so as to get rid
            # of superfluous requirements.
            # One approach is to first set the source to the (top) superobject then
            # shrink the source as needed according to the requirements arising from the compositions
            # in the `req`. This way the source of `req` here will be largest admissible one.
            # The requirement is generated when doing the composition and then is checked against the
            # previous `reqs` (when precomposing with the inclusion).
            nreqs[name] = (len(reqs), req)
            reqs.append(req)

        self.named_requirements = nreqs
        self.requirements = reqs

    def inclusion(self):
        return Inclusion(self, self.sup)

    @override
    def req(self, name: str):
        # Recall that `r.ssource.source` need not be `self.sup`.
        _, r = self.named_requirements[name]
        eq = r.compose_eq(Inclusion(self, r.ssource.source).ref())
        eq.proven = True
        return eq

    def identical(self, x: Obj):
        # Just like two morphisms can be the same without having the same hat,
        # two subobjects can be identical without having the same requirement
        # naming.
        return super().identical(x) or (
            isinstance(x, Subobject)
            and self.sup.identical(x.sup)
            and set(self.requirements) == set(x.requirements)
        )

    @override
    def diff(self, x: Obj):
        if super().identical(x):
            return 0

        sup = self.sup
        reqs = self.requirements
        if isinstance(x, Subobject):
            if sup.identical(x.sup):
                xreqs = x.requirements
                if set(reqs) >= set(xreqs):
                    return len(reqs) - len(xreqs)

            return -1

        if sup.identical(x):
            return len(reqs)

        return -1

    def hint(self):
        return self.sup, frozenset(self.requirements)

    def accepts(self, x: object):
        # That `x` is accepted by the source of `eq` is guaranteed by the order
        # of `self.requirements`.
        return self.sup.accepts(x) and all(
            eq.verify(x) for eq in self.requirements
        )

    def same(self, x: object, y: object):
        return self.sup.same(x, y)

    def proj(self, name: object) -> 'Mor':
        # The target of projections is never a subobject. This is fine, since
        # the needed object equalities are all registered, so that a lifting can
        # be done when needed.

        # If subobject is needed in requirement composition then the subobject
        # is recovered by the automatic restriction.
        return self.sup.proj(name)

class BaseSubobject(LexObj):
    __slots__ = ()

    def conversion(self, obj: Obj):
        return super().conversion(obj) or (
            self.diff(obj) > 0 and Inclusion(self, obj)
        ) or None

class Subobject2(BaseSubobject):
    """Models subobject

    A subobject is an object to which requirements have been associated.
    """
    __slots__ = 'sup', 'requirements', 'names', 'sup_len'
    sup: Obj
    requirements: list[Eq]
    names: dict[str, int]
    sup_len: int

    # def labeled_requirements(self) -> list[LabeledParallel]:
    #     """Requirements with labels"""
    #     reqs = [('', r) for r in self.requirements]

    #     for name, idx in self.names.items():
    #         reqs[idx] = (name, reqs[idx][1])

    #     return reqs

    def inclusion(self):
        return Inclusion(self, self.sup)

    def __init__(self, sup: Obj, requirements: Iterable[LabeledParallel]):
        self.sup = sup
        self.requirements = []
        self.names = {}
        names = self.names
        reqs = self.requirements

        for name, eq in requirements:
            if name:
                names[name] = len(reqs)

            reqs.append(eq)

        if isinstance(sup, Subobject | LexProduct):
            self.sup_len = sup.sup_len + len(sup.requirements)
        else:
            self.sup_len = 0

    @override
    def diff(self, x: Obj):
        # For simplicity this requires inclusion of one superobject in the other.
        # Whatever names appear on the subobject must also appear on the
        # superobject, unless they correspond to a requirement not belonging to
        # the superobject. This only recognizes inclusion in a product when the
        # `sup` is included in the product. The idea is that accounting for
        # requirements that are differently distributed along the superobject
        # hierarchy is too complicated.

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
        # with `where`. Inclusions without consistent naming must be explicitly built,
        # just like inclusions where the order of requirements is different.
        # Consistent naming ensures that the result is the same in the case of refactoring
        # by composing directly a morphism with the law (in which case no inclusion
        # would be involved), and if the result cannot be the same then an early failure
        # occurs. More flexibility is allowed by the fact that names don't reorder
        # requirements (like component names in product). If a name shows up in the
        # subobject and in the superobject then it must refer to the same equality.
        # A name can show up in the subobject but not in the superobject.
        s = super().diff(x)
        if s >= 0:
            return s

        sup = self.sup
        reqs = self.requirements
        if isinstance(x, Subobject):
            s = sup.diff(x.sup)
            if s >= 0:
                xreqs = x.requirements
                names = self.names
                xnames = x.names

                if set(reqs) >= set(xreqs) and all(
                    r not in xreqs or (
                        n in xnames and r.parallel(xreqs[xnames[n]])
                    ) for n, r in (
                        (n, reqs[i]) for n, i in names.items()
                    )
                ):
                    return s + len(reqs) - len(xreqs)

            return -1

        s = sup.diff(x)
        if s >= 0:
            return s + len(reqs)

        return -1

    @override
    def ireq(self, idx: int):
        reqs = self.requirements
        sup_len = self.sup_len
        if idx < sup_len:
            if idx < 0:
                raise ValueError("`name` of type `int` can't be negative.")

            return self.sup.ireq(idx)

        idx -= sup_len
        if idx >= len(reqs):
            raise ValueError("`name` of type `int` is too large.")

        eq = reqs[idx].compose_eq(Inclusion(self, self.sup).ref())
        eq.proven = True
        return eq

    @override
    def req(self, name: str):
        # TODO: !! Define LexProduct which handles flattening of component requirements!
        # Notice that in this case some isinstance(..., Subobject) checks will need to be
        # changed to isintance(..., LexProduct | Subobject).
        reqs = self.requirements
        names = self.names
        if name not in names:
            try:
                return self.sup.req(name)
            except TypeError as exc:
                raise ValueError(
                    "`name` does not correspond to any requirement",
                ) from exc

        idx = names[name]
        eq = reqs[idx].compose_eq(Inclusion(self, self.sup).ref())
        eq.proven = True
        return eq
        # TODO: target of inclusion must be partial object
        # Just directly use the source of the requirement. While the composition does
        # not undergo any check of source matching target, it is better to follow the
        # consistently.

    def identical(self, x: Obj):
        if super().identical(x):
            return True

        if isinstance(x, Subobject) and self.sup.identical(x.sup):
            reqs = self.requirements
            xreqs = x.requirements
            names = self.names
            xnames = x.names

            return (
                set(reqs) == set(xreqs) and len(names) == len(xnames) and all(
                    n in xnames and r.parallel(xreqs[xnames[n]])
                    for n, r in (
                        (n, reqs[i]) for n, i in names.items()
                    )
                )
            )

        return False

    def hint(self):
        return (
            type(self), self.sup, sum(hash(r) for r in self.requirements),
        )

    def accepts(self, x: object):
        return self.sup.accepts(x) and all(
            eq.verify(x) for eq in self.requirements
        )

    def same(self, x: object, y: object):
        return self.sup.same(x, y)

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

class Inclusion(CartMor):
    """Models inclusion"""
    # An inclusion where source and target are identical is at least
    # intensionally the same as the identity. Proving this however may not be
    # possible, since one does not allow subobjects without requirements.
    # It is then better to avoid creating identity inclusions, and in general
    # just create inclusions through the methods provided in this module, which
    # are guaranteed to produce valid inclusions.
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
    sup: Mor

    def after_incl(self, mor: 'Inclusion') -> Mor | tuple[Mor, Mor]:
        """Get supermorphism by composing with the inclusion"""
        target = mor.target
        sup = self.sup
        d = sup.target.diff(target)

        if d == 0:
            return sup

        if d > 0:
            return Inclusion(sup.target, target), sup

        # In this case `target` is supposed to be included in `sup.target`.
        assert target.diff(sup.target) > 0
        return EqualizerMor(sup, target)

    def __init__(
        self, mor: Mor, target: Obj,
    ):
        # When instantiating `ProductMor`, we may provide a `consistency`
        # argument. In contrast, here we never provide the equalities that prove
        # the parallel pairs, because unlike checking consistency checking the
        # forks is part of the theory. For this we use the binary operation
        # `equalizer_pairing`.
        super().__init__(mor.source, target)
        self.sup = mor

    def ev(self, x: object):
        return self.sup.ev(x)

    def hint(self):
        return self.target, self.sup

    def same(self, x: Mor):
        # The `self.sup` comparison can only be as conclusive as the
        # `self.target` comparison based on the `identical` method, so we use
        # `self.sup.same`.
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

class ProductSubobject(Product, BaseSubobject2):
    __slots__ = 'sup', 'requirements', 'named_requirements'

    def _extract_requirements(self, param: BaseSubobject2, proj: Mor):
        # TODO: compose with projection before updating (named_)requirements.
        # In the case of flattened product param, composition with projections
        # has already been done, but the projections have to be changed.
        # There is a theoretical way to do this. The flattened product param is
        # recovered through a projection pairing. Is the result of composing the
        # req projection with this projection pairing a renamed projection? Yes!
        # TODO: Initialization of product superobject should perhaps occur before
        # requirement extraction.
        inv_nreqs: dict[Eq, str] = {}
        for name, req in param.named_requirements.items():
            inv_nreqs[req] = name

        reqs = self.requirements
        nreqs = self.named_requirements
        for req in param.requirements:
            # TODO: It may be occur that this composition is mediated by lifting.
            # Liftings are only introduced automatically at the high-level.
            # Does this mean proj should have the original component as target
            # even if the component is a subobject?
            reqp = req.compose_eq(proj.ref())
            reqs.add(reqp)
            if req in inv_nreqs:
                nreqs[inv_nreqs[req]] = reqp

        return

    def _extract_requirements_from_params(self, params: Sequence[LabeledObj]):
        for name, param in params:
            if isinstance(name, tuple):
                assert isinstance(param, Product)
                if isinstance(param, ProductSubobject):
                    pass
                # Flattened product
                yield name, param
            else:
                # Flattened product when name is empty.
                yield name, param

    def __init__(self, params: Sequence[LabeledObj], flattened: bool = True):
        # TODO: All subobject params must be converted to their superobjects.
        # The requirements must be composed with the corresponding projections.
        self.requirements = set()
        self.named_requirements = {}
        super().__init__(
            list(self._extract_requirements(params)),
            flattened=flattened,
        )

LexObj.init_cls()
