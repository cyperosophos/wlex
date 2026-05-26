"""High level interface for cartesian ambient"""
from collections.abc import Sequence, Iterator
from typing import overload, Callable, TypeGuard, override
from itertools import chain, permutations

from .cells import Obj, Mor, Eq, MorStub
from . import category
from .category import EqLike, MorLike, Transformation, reduce, UnprovenEq, Once, Theory
from .public import cart as public
from .cells.cart import Product, ProductMor

class CartContext[T: Theory](category.Context[T]):
    """Handles cells of a theory with ambient cart"""
    __slots__ = ()

    terminal = staticmethod(public.terminal)
    terminal_mor = staticmethod(public.terminal_mor)
    terminal_mor_unique = staticmethod(public.terminal_mor_unique)
    product = staticmethod(public.product)
    pairing = staticmethod(public.pairing)
    pairing_unique = staticmethod(public.pairing_unique)
    pairing_eq = staticmethod(public.pairing_eq)

    tm = terminal_mor

    def imp(
        self, first: tuple[str | int, MorLike],
        *factors: tuple[str | int, MorLike],
    ):
        """Imperative composition"""
        # Polish order
        it = iter(reversed(list(chain((first,), factors))))

        fs: list[MorLike] = []
        for label, factor in it:
            if label == '':
                # This needs to be handled for the case when the target of factor
                # is not a product.
                fs.append(factor)
            else:
                fs.append(self.pair((label, factor)))

            break

        fs.extend(
            self.pair(('', self.identity), (l, f))
            for l, f in it
        )

        return self.c(*iter(fs))

    @override
    def register_equality(self, ssource: Mor, starget: Mor):
        super().register_equality(ssource, starget)

        # Only compose with projections that simplify both morphisms.
        # Register the whole equality regardless, since some projections may not
        # simplify. Register component equalities recursively, i.e. by calling
        # `self.register_equality`.
        if isinstance(ssource, ProductMor) and isinstance(starget, ProductMor):
            target = ssource.target
            assert target.identical(starget.target)
            labels = set(ssource.components) & set(starget.components)
            for label in labels:
                proj = target.proj(label)
                self.register_equality(
                    proj.compose(ssource),
                    proj.compose(starget),
                )

    def inverse_relabeling(
        self, obj: Obj,
        relabeling: Sequence[tuple[str | int, str | int]] | Sequence[str | int] | str | int,
    ):
        if isinstance(relabeling, (str, int)):
            if isinstance(obj.sup, Product):
                return (relabeling,)

            return ()

        if _all_tuple_label(relabeling):
            if isinstance(obj.sup, Product):
                return list(obj.inverse_relabeling(relabeling))

            return ()

        assert _all_label(relabeling)
        if not isinstance(obj.sup, Product):
            if len(relabeling) == 1:
                return relabeling[0]

            raise ValueError("Length must be 1.")

        return list(obj.inverse_relabeling(obj.sequence_relabeling(relabeling)))

    def with_labels(
        self, obj: Obj,
        relabeling: Sequence[tuple[str | int, str | int]] | Sequence[str | int] | str | int,
    ):
        if isinstance(relabeling, (str, int)):
            if isinstance(obj.sup, Product):
                return obj.proj(relabeling).target

            return obj.terminal()

        if _all_tuple_label(relabeling):
            if isinstance(obj.sup, Product):
                return obj.with_labels(relabeling)

            return obj.terminal()

        assert _all_label(relabeling)
        if not isinstance(obj.sup, Product):
            if len(relabeling) == 1:
                return self.prod((relabeling[0], obj))

            raise ValueError("Length must be 1.")

        return obj.with_labels(obj.sequence_relabeling(relabeling))

    def relabel(
        self, obj: Obj,
        relabeling: Sequence[tuple[str | int, str | int]] | Sequence[str | int] | str | int,
    ):
        if isinstance(relabeling, (str, int)):
            if isinstance(obj.sup, Product):
                return obj.proj(relabeling)

            return obj.terminal_mor()

        if _all_tuple_label(relabeling):
            if isinstance(obj.sup, Product):
                return obj.relabel(relabeling)

            return obj.terminal_mor()

        assert _all_label(relabeling)
        if not isinstance(obj.sup, Product):
            if len(relabeling) == 1:
                return self.pair((relabeling[0], obj))

            raise ValueError("Length must be 1.")

        return obj.relabel(obj.sequence_relabeling(relabeling))

    @overload
    def l(
        self, mor: Obj,
        relabeling: Sequence[tuple[str | int, str | int]] | Sequence[str | int] | str | int,
    ) -> Obj: ...
    @overload
    def l(
        self, mor: Mor,
        relabeling: Sequence[tuple[str | int, str | int]] | Sequence[str | int] | str | int,
    ) -> Mor: ...
    @overload
    def l(
        self, mor: Transformation,
        relabeling: Sequence[tuple[str | int, str | int]] | Sequence[str | int] | str | int,
    ) -> Transformation: ...
    @overload
    def l(
        self, mor: Eq,
        relabeling: Sequence[tuple[str | int, str | int]] | Sequence[str | int] | str | int,
    ) -> Eq: ...

    def l(
        self, mor: EqLike,
        relabeling: Sequence[tuple[str | int, str | int]] | Sequence[str | int] | str | int,
    ) -> EqLike:
        def l_mor(m: Mor):
            return self.c(self.relabel(m.target, relabeling), m)

        if isinstance(mor, Obj):
            # TODO: This is not the same as setting mor to the identity of the object.
            # Inconsistency!
            return self.with_labels(mor, relabeling)

        # TODO: It seems there is no need to override this in LexContext,
        # because projection simplification allows easily finding the proofs.
        if isinstance(mor, Mor):
            return l_mor(mor)

        if isinstance(mor, Callable):
            # TODO: use functools.wrapper to ease debugging
            def _t(source: Obj):
                return l_mor(mor(source))

            return _t

        return self.c(
            self.relabel(mor.ssource.target, relabeling),
            mor,
        )

    @overload
    def ix(self, mor: Obj | Mor) -> Mor: ...
    @overload
    def ix(self, mor: Transformation) -> Transformation: ...
    @overload
    def ix(self, mor: Eq) -> Eq: ...

    def ix(self, mor: EqLike) -> EqLike:
        # This this not need to be overriden in LexContext in order to take
        # requirementes into account, because `c` already takes care of fitting.
        def relabel(source: Product):
            labels = list(source.components)
            new = source.with_labels(
                source.sequence_relabeling(list(range(len(labels)))),
            )
            return new.relabel(new.sequence_relabeling(labels))

        def ix_mor(m: Mor):
            source = m.source.sup
            if not isinstance(source, Product):
                return m

            return self.c(m, relabel(source))

        if isinstance(mor, Obj):
            if not isinstance(mor.sup, Product):
                return mor

            return self.c(mor, mor.with_labels(
                mor.sequence_relabeling(list(range(len(mor.sup.components)))),
            ))

        if isinstance(mor, Mor):
            return ix_mor(mor)

        if isinstance(mor, Callable):
            def _t(source: Obj):
                return ix_mor(mor(source))

            return _t

        source = mor.ssource.source.sup
        if not isinstance(source, Product):
            return mor

        return self.c(mor, relabel(source))

    def _prove_pairing_eq(self, ssource: ProductMor, starget: ProductMor) -> Eq:
        # First step is to prove each component equality.
        length = len(ssource.components)
        if length != len(starget.components):
            raise UnprovenEq("Can't prove equality of pairings with different length")

        # Can't prove equality if there are too many unlabeledd components
        full_length = ssource.components.full_len()
        if full_length != starget.components.full_len():
            raise UnprovenEq("Can't prove equality of pairings with different unlabeled components")

        if full_length - length > 5: # Hardcoded!
            raise UnprovenEq("Can't prove equality of pairings with too many unlabeled components")

        labels = set(ssource.components)
        if labels != set(starget.components):
            raise UnprovenEq("Can't prove equality of pairings with different labels")

        # Prove equality of labeled components
        eqs = (
            (label, self.prove(
                ssource.components[label],
                starget.components[label],
            )) for label in labels
        )

        unlabeled = [
            mor
            for label, mor in ssource.components.full_items()
            if label == ''
        ]
        unlabeled_t = [
            mor
            for label, mor in starget.components.full_items()
            if label == ''
        ]
        unlabeled_eqs: list[Eq] = []
        for perm in permutations(unlabeled):
            for s, t in zip(perm, unlabeled_t):
                try:
                    e = self.prove(s, t)
                except UnprovenEq:
                    unlabeled_eqs = []
                    break

                unlabeled_eqs.append(e)
            else:
                assert len(unlabeled_eqs) == len(unlabeled)
                break
        else:
            raise UnprovenEq("Tried all permutations of unlabeled components")

        return self.pair(*chain(eqs, (('', e) for e in unlabeled_eqs)))

    def prove(self, ssource: Mor, starget: Mor, _fork: bool = True) -> Eq:
        try:
            return super().prove(ssource, starget, _fork=_fork)
        except UnprovenEq:
            # Handle extensional `pairing_eq`
            if isinstance(ssource, ProductMor) and isinstance(starget, ProductMor):
                return self._prove_pairing_eq(ssource, starget)

            raise

    @staticmethod
    def proj(name: str | int):
        """Create projection transformation from name"""
        def _proj(source: Obj):
            return source.proj(name)

        return _proj

    @overload
    def el(
        self, name: str, cell_or_stub: MorLike | Once[MorStub], target: Obj,
    ) -> Mor: ...
    @overload
    def el(
        self, name: str, cell_or_stub: Obj | Mor, target: None = None,
    ) -> Mor: ...

    def el(
        self, name: str, cell_or_stub: MorLike | Once[MorStub], target: Obj | None = None,
    ):
        """Sets name on element and checks its type

        An element is a morphism from the terminal object.
        """
        if target:
            return self.mor(
                name, cell_or_stub,
                (self.terminal(type(target)), target),
            )

        assert isinstance(cell_or_stub, (Obj, Mor))
        return self.mor(name, cell_or_stub)

    def _pair(self, mors: tuple[Mor, Mor]):
        # Wrap `public.pairing` so that it can be used as binary `comp` in
        # `_pairing`.
        return self.pairing(mors)[0]

    def _pair_eq(self, eqs: tuple[Eq, Eq]):
        p_eq, q_eq = eqs
        x = (p_eq.ssource, q_eq.ssource)
        y = (p_eq.starget, q_eq.starget)
        return self.pairing_eq((x, y, p_eq, q_eq))

    def _pair_op_mor(
        self, first: MorLike, factors: Sequence[MorLike],
    ) -> Mor | Transformation:
        # Used in method `pairing`.
        return _pairing(self._pair, first, factors)

    def _pair_op_eq(
        self, first: EqLike, factors: Sequence[EqLike],
    ) -> Eq:
        return _pairing_eq(self._pair_eq, first, factors)

    @overload
    def pair(
        self,
        first: Mor | Obj,
        *factors: Mor | Obj,
    ) -> Mor: ...
    @overload
    def pair(
        self,
        first: MorLike,
        *factors: MorLike,
    ) -> Mor | Transformation: ...
    @overload
    def pair(
        self,
        first: Eq,
        *factors: EqLike,
    ) -> Eq: ...
    @overload
    def pair(
        self,
        first: MorLike,
        *factors: Eq,
    ) -> Eq: ...
    @overload
    def pair(
        self,
        first: tuple[str | int, Mor | Obj],
        *factors: tuple[str | int, Mor | Obj],
    ) -> Mor: ...
    @overload
    def pair(
        self,
        first: tuple[str | int, MorLike],
        *factors: tuple[str | int, MorLike],
    ) -> Mor | Transformation: ...
    @overload
    def pair(
        self,
        first: tuple[str | int, Eq],
        *factors: tuple[str | int, EqLike],
    ) -> Eq: ...
    @overload
    def pair(
        self,
        first: tuple[str | int, MorLike],
        *factors: tuple[str | int, Eq],
    ) -> Eq: ...

    def pair(
        self,
        first: tuple[str | int, EqLike] | EqLike,
        *factors: tuple[str | int, EqLike] | EqLike,
    ) -> Mor | Transformation | Eq:
        """Variadic high-level pairing"""

        if isinstance(first, (Mor, Obj, Callable, Eq)):
            assert _all_unlabeled(factors)
            first = (0, first)
            factors = tuple(zip(range(1, len(factors) + 1), factors))
        else:
            assert _all_labeled(factors)

        return self.labeled_pair(first, *factors)

    def labeled_pair(
        self,
        first: tuple[str | int, EqLike],
        *factors: tuple[str | int, EqLike],
    ) -> Mor | Transformation | Eq:
        # A consistent even if somewhat cumbersome way of providing factors
        # (namely as tuples containing the label and the factor) makes sense,
        # since theories written in python are just transpilations of wlex.
        res = category.operate_mor_or_eq(
            self._pair_op_mor, self._pair_op_eq, first[1], [f for _, f in factors],
        )
        labels = [l for l, _ in chain((first,), factors)]
        if isinstance(res, Mor):
            assert isinstance(res, ProductMor)
            return res.idx_to_labels(labels)

        if isinstance(res, Callable):
            def _pair(source: Obj):
                m = res(source)
                assert isinstance(m, ProductMor)
                return m.idx_to_labels(labels)

            return _pair

        assert isinstance(res.ssource, ProductMor)
        assert isinstance(res.starget, ProductMor)
        eq = Eq(
            res.ssource.idx_to_labels(labels),
            res.starget.idx_to_labels(labels),
        )
        eq.proven = res.proven
        return eq

    def _produce(self, objs: tuple[Obj, Obj]):
        return self.product(objs)[0].source

    def labeled_prod(
        self, first: tuple[str | int, Obj],
        *params: tuple[str | int, Obj],
    ) -> Obj:
        # The point of the next line is to use the undelying theory.
        reduce(self._produce, chain((first[1],), (f for _, f in params)))
        res = first[1].vproduct(list(chain((first,), params)))
        return res

    @overload
    def prod(
        self, first: Obj,
        *params: Obj,
    ) -> Obj: ...
    @overload
    def prod(
        self, first: tuple[str | int, Obj],
        *params: tuple[str | int, Obj],
    ) -> Obj: ...

    def prod(
        self, first: tuple[str | int, Obj] | Obj,
        *params: tuple[str | int, Obj] | Obj,
    ) -> Obj:
        """Variadic high-level products"""

        if isinstance(first, Obj):
            assert _all_unlabeled(params)
            first = (0, first)
            params = tuple(zip(range(1, len(params) + 1), params))
        else:
            assert _all_labeled(params)

        return self.labeled_prod(first, *params)

def _all_tuple_label[T](
    labels: Sequence[tuple[T, T]] | Sequence[T],
) -> TypeGuard[Sequence[tuple[T, T]]]:
    return not labels or (len(labels) > 0 and isinstance(labels[0], tuple))

def _all_label[T](
    labels: Sequence[tuple[T, T]] | Sequence[T],
) -> TypeGuard[Sequence[T]]:
    return not labels or (len(labels) > 0 and not isinstance(labels[0], tuple))

def _all_unlabeled[T](
    params: tuple[tuple[str | int, T] | T, ...],
) -> TypeGuard[tuple[T, ...]]:
    return all(not isinstance(param, tuple) for param in params)

def _all_labeled[T](
    params: tuple[tuple[str | int, T] | T, ...],
) -> TypeGuard[tuple[tuple[str | int, T], ...]]:
    return all(isinstance(param, tuple) for param in params)

def _unlabeled[T](factors: Iterator[T]) -> Sequence[tuple[int, T]]:
    return tuple(enumerate(factors))

def _pairing(
    comp: category.Composer[Mor],
    first: MorLike,
    factors: Sequence[MorLike],
) -> Mor | Transformation:
    # This creates the pairing using binary `comp`, which will typically be (a
    # wrapping of) the `pairing` method of context (`public.pairing`).
    def op(it: Iterator[Mor]):
        return _mor_pairing(comp, it)

    return category.operate_mor_common_source(op, first, factors)

def _pairing_eq(
    comp: category.Composer[Eq],
    first: EqLike,
    factors: Sequence[EqLike],
) -> Eq:
    def op(it: Iterator[Eq]):
        return _eq_pairing(comp, it)

    return category.operate_eq_common_source(op, first, factors)

def _mor_pairing(comp: category.Composer[Mor], factors: Iterator[Mor]):
    # Applies `comp` on factors (only for type checking), then create pairing
    # using the variadic pairing method tied to the source so that empty labels
    # are included. The actual labels get set in method Context.pair.
    # Flattening must be skipped here. The flattened product is created in
    # `_labeled_product_mor`.
    args = list(factors)
    res = reduce(comp, iter(args))
    return res.source.vproduct_mor(_unlabeled(iter(args)))

def _eq_pairing(comp: category.Composer[Eq], factors: Iterator[Eq]):
    args = list(factors)
    res = reduce(comp, iter(args))
    source = res.ssource.source
    return Eq(
        source.vproduct_mor(_unlabeled(f.ssource for f in args)),
        source.vproduct_mor(_unlabeled(f.starget for f in args)),
    )
