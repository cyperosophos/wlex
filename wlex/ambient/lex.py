"""High level interface fo the lex ambient"""
from itertools import chain
from typing import override, TypeGuard
from collections.abc import Iterator, Sequence, Callable

from .cells import Obj, Mor, Eq
from . import cart
from .category import EqLike, MorLike, reduce, UnprovenEq, Transformation, Theory
from .cells.cart import Product
from .cells.lex import EqualizerMor
from .public import lex as public

# TODO: When implementing extensive context recall the relation between
#       restriction and overloading.

class LexContext[T: Theory](cart.CartContext[T]):
    """Handles cells of a theory with ambient lex"""
    __slots__ = ()

    equalizer = staticmethod(public.equalizer)
    equalizer_pairing = staticmethod(public.equalizer_pairing)
    equalizer_pairing_unique = staticmethod(public.equalizer_pairing_unique)
    equalizer_pairing_eq = staticmethod(public.equalizer_pairing_eq)

    def with_labels(self, obj: Obj, relabeling: dict[str | int, str | int] | Sequence[str | int]):
        prod = obj.sup.with_labels(relabeling)
        # No assumption about order of labels in relabeling being the same as in
        # the components of prod.

        r = prod.relabel(obj.sup.invert_relabeling(relabeling))
        assert r.target.identical(obj.sup)
        return self.req(
            prod, *((
                self.c(s, r),
                self.c(t, r),
            ) for s, t in obj.requirements),
        )

    l = with_labels

    def _straighten_mors(self, factors: Iterator[Mor]):
        # Polish order
        it = iter(factors)
        straight: list[Mor] = []
        for f in it:
            straight.append(f)
            source = f.target
            break
        else:
            assert False

        for f in it:
            if f.source.identical(source):
                straight.append(f)
            else:
                assert f.source.sup.identical(source.sup)
                straight = [
                    self.fit(f.source.vcomposition(
                        *reversed(straight),
                    ), f.source), f,
                ]

            source = f.target

        return iter(straight)

    def _straighten_eqs(self, factors: Iterator[Eq]):
        # Polish order
        it = iter(factors)
        straight: list[Eq] = []
        for f in it:
            straight.append(f)
            source = f.ssource.target
            break
        else:
            assert False

        for f in it:
            if f.ssource.source.identical(source):
                straight.append(f)
            else:
                assert f.ssource.source.sup.identical(source.sup)
                straight = [
                    self.fit_eq(reduce(self.compose_eq,
                        reversed(straight),
                    ), f.ssource.source), f,
                ]

            source = f.ssource.target

        return iter(straight)

    def comp_op_mor(
        self, first: MorLike, factors: Sequence[MorLike],
        straighten: Callable[[Iterator[Mor]], Iterator[Mor]] | None = None,
    ):
        return super().comp_op_mor(
            first, factors,
            straighten=straighten or self._straighten_mors,
        )

    def comp_op_eq(
        self, first: EqLike, factors: Sequence[EqLike],
        straighten: Callable[[Iterator[Eq]], Iterator[Eq]] | None = None,
    ):
        return super().comp_op_eq(
            first, factors,
            straighten=straighten or self._straighten_eqs,
        )

    def _restricted_source(self, mor: Mor, target: Obj):
        missing = target.requirements - mor.target.requirements
        source = self.req(mor.source, *(
            (self.c(ssource, mor), self.c(starget, mor))
            for ssource, starget in missing
        ))
        return source

    def _restricted_sup(self, mor: Mor, target: Obj):
        extra = mor.target.requirements & target.requirements
        return mor.target.sup.subobject(extra)

    def fit(self, mor: Mor, target: Obj):
        # The source of a requirement of `target` is a *strict* superobject of
        # target and a subobject of `target.sup` (possibly `target.sup` itself).
        # The only condition on `mor` is `target.sup.identical(mor.target.sup)`.
        # `mor.target` can have requirements that aren't fulfilled by `target`.
        # These get ignored.
        source = self._restricted_source(mor, target)

        # Greatest common superobject
        sup = self._restricted_sup(mor, target)

        # Redundant type checking: lift, incl and compose are guaranteed to
        # receive the right type of arguments here. We still type-check lift
        # though `equalizer_pairing`. The forks to check include tautological
        # forks. Some parallel pairs have a subset of `sup` as their source.
        # The approach here is to lift `long` after each call to
        # `equalizer_pairing`. We assume that `target.requirements` come in
        # the right order. This is justified by the way we've implemented
        # `req`. Type-checking would fail if this was not the case.
        long = mor.target.incl(sup).compose(
            mor.compose(source.incl(mor.source)),
        )
        short = long

        for ssource, starget in target.requirements:
            # We need to make sure that the parallel pair can be precomposed
            # with short. The source of the parallel pair is a (non-strict)
            # subobject of `target.sup` and a strict superobject of `target`.
            # The initial target of `short` is a superobject of `target` and
            # a subobject of `target.sup.` Requirements keep getting added
            # after each call to `equalizer_pairing` until the target of
            # `short` is `target` itself.

            # We rely on forks from `source` already being registered. This way
            # we also cover tautological forks. We use `self.c` here. Since
            # `short.source` should remain identical, i.e. `source`, which
            # already has all the needed requirements, we assert that
            # `handle.source` remains identical to `source.` Fitting the source
            # of the parallel pair would in contrast make no sense, since we
            # would only be able to have the target remain the same but not the
            # new fitted source.
            handle = self.c(ssource.source, short)
            assert handle.source.identical(source)
            eq = self.prove(
                *Eq(ssource, starget).compose_eq(
                    handle.ref(),
                ).ssignature(),
            )
            fork = (
                handle, ssource, starget, eq,
            )
            short, _, _, _, _, _ = self.equalizer_pairing(fork)

        # When `mor.target` is a subobject of `target`, `lift` has no effect.
        res = target.lift(long)
        assert res.same(short) #TODO: this is quadratic, so only call when debugging!
        return res

    def fit_eq(self, eq: Eq, target: Obj) -> Eq:
        # This is required in order to be able to compose equalities when only
        # the superobjects match.
        source = self._restricted_source(eq.ssource, target)
        sup = self._restricted_sup(eq.ssource, target)
        long = eq.ssource.target.incl(sup).ref().compose_eq(
            eq.compose_eq(source.incl(eq.ssource.source).ref()),
        )
        short = long

        for ssource, starget in target.requirements:
            handle = self.c(ssource.source, short)
            assert handle.ssource.source.identical(source)
            eq_s = self.prove(
                *Eq(ssource, starget).compose_eq(
                    handle.ssource.ref(),
                ).ssignature(),
            )
            eq_t = self.prove(
                *Eq(ssource, starget).compose_eq(
                    handle.ssource.ref(),
                ).ssignature(),
            )
            fork_eq = (
                handle.ssource, ssource, starget, eq_s,
                handle.starget, eq_t,
                handle,
            )
            short = self.equalizer_pairing_eq(fork_eq)

        return short

    def req(
        self, obj: Obj,
        first: tuple[MorLike, MorLike],
        *requirements: tuple[MorLike, MorLike],
    ) -> Obj:
        # When type-checking with `equalizer`, the parallel pair gets precomposed
        # with an inclusion as needed so that its source is the `obj` with all the
        # previous requirements. The problem with this is that requirements don't
        # necessarily come in the right order. The solution is then to have any
        # unmet requirements coming from a requirement source be automatically
        # imposed on `obj`. The requirements passed to the `subobject` method keep
        # their original source. The important thing is that a fork can be formed
        # with an inclusion from the resulting subobject and the parallel pair
        # corresponding to a requirement. The result must be independent of the
        # order of the requirements.

        # Convert all `MorLike` to `Mor` in parallel pairs. Source need not be
        # preserved, so further checking is still needed. Use `obj` as the
        # source regardless of any previous requirements (order of requirements
        # does not affect result). Exclude all tautologies including fork
        # tautologies. All requirements must be included in the `proven_eqs`.

        reqs: set[tuple[Mor, Mor]] = set()
        for ssource, starget in chain((first,), requirements):
            # This type-checks that source of parallel pair is (a subobject of)
            # `obj`.
            ssource = self.c(ssource, obj)
            starget = self.c(starget, obj)

            try:
                self.prove(ssource, starget)
            except UnprovenEq:
                # Call `public.equalizer` for type-checking the parallel pair.
                mor, _, _, eq = self.equalizer((ssource, starget))

                # We register the shortest fork.
                self.eq(eq)

                # ...The idea here is to register the fork in case one needs its proof.
                # The problem is that the fork may still be valid even with smaller sources.
                # A fork consists of an inclusion (the handle) and a parallel pair.
                # Is it possible to have a parallel pair that comes precomposed with an
                # inclusion, so that the handle doesn't reach the top of the (composed)
                # inclusion (the intersection of the two inclusions corresponding to each
                # arrow of the parallel pair)? aji = bji => aj = bj? No!
                # If aj = bj is true, then it must be registered instead of aji = bji,
                # but this is limitted by what it's actually known. We simply strive to
                # register the most general equalities. We find aji = bji by extending the
                # handle.

                # Requirements imposed by sources of parallel pairs are not
                # being type-checked by `equalizer`, but this is ok since they
                # must have past the type-checking when creating the source of
                # the parallel pair, and all we need the source of the parralel
                # pair is the correct one (i.e. that it has the same superobject
                # as `obj`).
                reqs.update(mor.source.requirements)

        return obj.subobject(reqs)

    # def restrict(self, mor: Mor, target: Obj):
    #     # This has to be used after conversion has been inferred, so that
    #     # `target` is a (strict) subobject of `mor.target`.


    #     # TODO: Type checking here or make this private.
    #     #       The condition is target.sup.identical(mor.target.sup)
    #     #       What happens if some of the requirements are already
    #     #       fulfilled by mor.target??
    #     #       What should happen is that the lifting has no effect for
    #     #       such requirements, or rather that the subobject skips such
    #     #       requirements, because in their version precomposed with `mor`
    #     #       they are already implied by the existing requirements?
    #     # TODO: Handle case where target is too large? (only mediating inclusion is needed)
    #     # TODO: Some EqualizerMor are extensionally equal to their supermorphism.
    #     #       Some inclusions are extensionally identities.

    #     if mor.target.identical(target):
    #         return mor

    #     # Restricting means precomposing with an inclusion to allow lifting to a
    #     # subobject.
    #     requirements = target.requirements - mor.target.requirements
    #     if not requirements:
    #         # TODO: Handle with conversion!
    #         return mor.target.incl(target).compose(mor)

    #     source = Subobject(mor.source, (
    #         (ssource.compose(mor), starget.compose(mor))
    #         for ssource, starget in requirements
    #     ))

    #     return EqualizerMor(mor.compose(source.incl(mor.source)), target)

    def _prove_equalizer_pairing_eq(self, ssource: EqualizerMor, starget: EqualizerMor) -> Eq:
        eq = self.prove(ssource.sup, starget.sup)
        target = ssource.target
        if target.identical(starget.target):
            return self.fit_eq(eq, target)

        raise UnprovenEq("Targets don't match.")

    def prove(self, ssource: Mor, starget: Mor, _fork: bool = True) -> Eq:
        try:
            return super().prove(ssource, starget, _fork=_fork)
        except UnprovenEq:
            if isinstance(ssource, EqualizerMor) and isinstance(starget, EqualizerMor):
                return self._prove_equalizer_pairing_eq(ssource, starget)

            raise

    @override
    def labeled_prod(self, first: tuple[str | int, Obj], *params: tuple[str | int, Obj]):
        # Extract requirements of all subobject components and use them to turn
        # the product into a subobject of the product.
        sup = super().labeled_prod(
            *((l, p.sup) for l, p in chain((first,), params)),
        )

        if all(p is p.sup for _, p in chain((first,), params)):
            return sup

        assert isinstance(sup, Product)
        requirements = chain(*((
            (self.c(s, proj), self.c(t, proj))
            for s, t in reqs
        ) for proj, reqs in (
            (sup.proj(l), c.requirements)
            for l, c in sup.components.items()
        )))

        return self.req(sup, *requirements)

    @override
    def labeled_pair(
        self,
        first: tuple[str | int, EqLike],
        *factors: tuple[str | int, EqLike],
    ):
        components: list[tuple[str | int, Obj] | None] = []

        def wrap_transformation(idx: int, label: str | int, factor: Transformation):
            def wrapper(x: Obj):
                mor = factor(x)
                target = mor.target
                # This means `wrapper` gets called only once.
                assert components[idx] is None
                components[idx] = (label, target)
                return self.c(target.incl(), mor)

            return wrapper

        def handle_factor(idx: int, label: str | int, factor: EqLike):
            # This can only be called once due to side effect on `components`.
            # Preserve the source
            assert len(components) == idx

            if isinstance(factor, Callable):
                components.append(None)
                return label, wrap_transformation(idx, label, factor)

            if isinstance(factor, Obj):
                target = factor
            elif isinstance(factor, Mor):
                target = factor.target
            else:
                target = factor.ssource.target

            components.append((label, target))
            return label, self.c(target.incl(), factor)

        sup = super().labeled_pair(
            *(handle_factor(i, *f) for i, f in enumerate(chain((first,), factors))),
        )

        if isinstance(sup, Callable):
            def wrapper(x: Obj):
                mor = sup(x)
                assert _all_labeled_obj(components)
                target = self.labeled_prod(*iter(components))
                restricted = self.c(target, mor)
                assert target.sup.identical(mor.target)
                assert restricted.source.identical(mor.source)
                return restricted

            return wrapper

        assert _all_labeled_obj(components)
        target = self.labeled_prod(*iter(components))
        restricted = self.c(target, sup)

        if isinstance(sup, Mor):
            assert target.sup.identical(sup.target)
            assert isinstance(restricted, Mor)
            assert restricted.source.identical(sup.source)
        else:
            assert target.sup.identical(sup.ssource.target)
            assert isinstance(restricted, Eq)
            assert restricted.ssource.source.identical(sup.ssource.source)

        return restricted

def _all_labeled_obj(
    factors: Sequence[tuple[str | int, Obj] | None],
) -> TypeGuard[Sequence[tuple[str | int, Obj]]]:
    return all(isinstance(f, tuple) for f in factors)
