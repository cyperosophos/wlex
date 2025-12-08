"""High level interface for cartesian ambient"""
from collections.abc import Sequence, Callable, Iterator
from typing import TypeGuard, overload, NoReturn
from itertools import chain
from operator import attrgetter

from .cells import Obj, Mor, Eq
from . import category
from .category import EqLike, MorLike, Transformation, operate_mor_or_eq, reduce
from .public import cart as public
from .cells.cart import Product, ProductMor, LabeledObj, Label

LabeledOptionalObj = tuple[str, Obj | None] | tuple[tuple[str, ...], Product]

class Context(category.Context):
    """Handles cells of a theory with ambient cart"""
    __slots__ = ()

    terminal = Product(())
    product = staticmethod(public.product)
    pairing = staticmethod(public.pairing)
    pairing_eq = staticmethod(public.pairing_eq)

    @staticmethod
    def proj(name: object):
        """Create projection transformation from name"""
        def _proj(source: Obj):
            return source.proj(name)

        return _proj

    def el(self, name: str, cell: MorLike | None, target: Obj | None = None):
        """Sets name on element and checks its type

        An element is a morphism from the terminal object.
        """
        return self.mor(name, cell, target and (self.terminal, target))

_get_source = attrgetter('source')

def _unlabeled[T](factors: Iterator[T]) -> Sequence[tuple[Label, T]]:
    return [('', f) for f in factors]

def _pairing(
    comp: category.Composer[Mor],
    first: MorLike,
    factors: Sequence[MorLike],
) -> Mor | Transformation:
    factor_it = chain((first,), factors)

    # Conversion is done adapting the source from left to right.
    # See: `category._gen_fit_eqs_for_trans` which adapts in the opposite
    # direction.
    if isinstance(first, Callable):
        def _pair(source: Obj):
            return _mor_pairing(
                comp, category.gen_fit_mors(source, factor_it, _get_source),
            )

        return _pair

    if isinstance(first, Obj):
        source = first
    else:
        source = first.source

    return _mor_pairing(
        comp, category.gen_fit_mors(source, factor_it, _get_source),
    )

def _pairing_eq(
    comp: category.Composer[Eq],
    first: EqLike,
    factors: Sequence[EqLike],
) -> Eq:
    if isinstance(first, Callable):
        raise TypeError(
            "Transformation is not allowed as the first factor of a pairing "
            "containing equalities."
        )

    if isinstance(first, Obj):
        source = first
    elif isinstance(first, Mor):
        source = first.source
    else:
        source = first.ssource.source

    factor_it = chain((first,), factors)
    return _eq_pairing(
        comp, category.gen_fit_eqs(source, factor_it, _get_source),
    )

def _mor_pairing(comp: category.Composer[Mor], factors: Iterator[Mor]):
    args = list(factors)
    res = reduce(comp, iter(args))
    return ProductMor(res.source, _unlabeled(iter(args)), flattened=False)

def _eq_pairing(comp: category.Composer[Eq], factors: Iterator[Eq]):
    args = list(factors)
    res = reduce(comp, iter(args))
    source = res.ssource.source
    return Eq(
        ProductMor(source, _unlabeled(f.ssource for f in args), flattened=False),
        ProductMor(source, _unlabeled(f.starget for f in args), flattened=False),
    )

def _labeled_product_mor(
    unlabeled: Mor, labeled_params: Sequence[tuple[Label, object]],
    consistency: Sequence[Eq],
):
    assert isinstance(unlabeled, ProductMor)
    assert len(labeled_params) == len(unlabeled.components)
    return ProductMor(unlabeled.source, [
        (label, component)
        for (label, _), (_, component)
        in zip(labeled_params, unlabeled.components)
    ], consistency)

def pairer(ctx: Context):
    """Create function for variadic high-level pairing"""

    def pair(mors: tuple[Mor, Mor]):
        return ctx.pairing(mors)[0]

    def pair_eq(eqs: tuple[Eq, Eq]):
        p_eq, q_eq = eqs
        x = (p_eq.ssource, q_eq.ssource)
        y = (p_eq.starget, q_eq.starget)
        return ctx.pairing_eq((x, y, p_eq, q_eq))

    def op_mor(
        first: MorLike, factors: Sequence[MorLike],
    ) -> Mor | Transformation:
        return _pairing(pair, first, factors)

    def op_eq(
        first: EqLike, factors: Sequence[EqLike],
    ) -> Eq:
        return _pairing_eq(pair_eq, first, factors)

    @overload
    def pairing(
        consistency: Sequence[Eq],
        first: tuple[Label, MorLike | None],
        *factors: tuple[Label, MorLike | None],
    ) -> Mor | Transformation: ...
    @overload
    def pairing(
        consistency: Sequence[Eq],
        first: tuple[Label, Eq],
        *factors: tuple[Label, EqLike | None],
    ) -> Eq: ...
    @overload
    def pairing(
        consistency: Sequence[Eq],
        first: tuple[Label, MorLike],
        *factors: tuple[Label, Eq],
    ) -> Eq: ...
    @overload
    def pairing(
        consistency: Sequence[Eq],
        first: tuple[Label, None],
        *factors: tuple[Label, EqLike | None],
    ) -> NoReturn: ...

    def pairing(
        consistency: Sequence[Eq],
        first: tuple[Label, EqLike | None],
        *factors: tuple[Label, EqLike | None],
    ) -> Mor | Transformation | Eq:
        # A uniform even if somewhat cumbersome way of providing factors (namely
        # as tuples containing the label and the factor) makes sense, since
        # theories written in python are just transpilations of wlex.
        if not factors:
            raise ValueError("At least two components must be provided.")

        res = operate_mor_or_eq(
            op_mor, op_eq, first[1], [f for _, f in factors],
        )

        if isinstance(res, Mor):
            return _labeled_product_mor(res, factors, consistency)

        if isinstance(res, Callable):
            def _pair(source: Obj):
                return _labeled_product_mor(res(source), factors, consistency)

            return _pair

        return Eq(
            _labeled_product_mor(res.ssource, factors, consistency),
            _labeled_product_mor(res.starget, factors, consistency),
        )

    return pairing

def _all_eq(factors: Sequence[EqLike]) -> TypeGuard[Sequence[Eq]]:
    return all(isinstance(f, Eq) for f in factors)

def _all_labeled_obj(
    params: Sequence[LabeledOptionalObj],
) -> TypeGuard[Sequence[LabeledObj]]:
    return all(f is not None for _, f in params)

def _is_labeled_obj(lo: LabeledOptionalObj) -> TypeGuard[LabeledObj]:
    return lo[1] is not None

def pairer0(ctx: Context):
    "Same as `pairer` but without `consistency` argument"
    orig_pairing = pairer(ctx)

    @overload
    def pairing(
        first: tuple[Label, MorLike | None],
        *factors: tuple[Label, MorLike | None],
    ) -> Mor | Transformation: ...
    @overload
    def pairing(
        first: tuple[Label, Eq],
        *factors: tuple[Label, EqLike | None],
    ) -> Eq: ...
    @overload
    def pairing(
        first: tuple[Label, MorLike],
        *factors: tuple[Label, Eq],
    ) -> Eq: ...
    @overload
    def pairing(
        first: tuple[Label, None],
        *factors: tuple[Label, EqLike | None],
    ) -> NoReturn: ...

    def pairing(
        first: tuple[Label, EqLike | None],
        *factors: tuple[Label, EqLike | None],
    ) -> Mor | Transformation | Eq:
        first_label = first[0]
        factor_labels = [label for label, _ in factors]

        def op_mor(
            first: MorLike, factors: Sequence[MorLike],
        ) -> Mor | Transformation:
            return orig_pairing(
                (), (first_label, first), *list(zip(factor_labels, factors)),
            )

        def op_eq(
            first: EqLike, factors: Sequence[EqLike],
        ) -> Eq:
            if isinstance(first, Eq):
                return orig_pairing(
                    (), (first_label, first), *list(zip(factor_labels, factors)),
                )
            assert _all_eq(factors)
            return orig_pairing(
                (), (first_label, first), *list(zip(factor_labels, factors)),
            )

        return operate_mor_or_eq(
            op_mor, op_eq,
            first[1], [f for _, f in factors],
        )

    return pairing

def producer(ctx: Context):
    """Creates function for variadic high-level products"""

    def produce(objs: tuple[Obj, Obj]):
        return ctx.product(objs)[0].source

    def product(first: LabeledOptionalObj, *params: LabeledOptionalObj) -> Product:
        if _is_labeled_obj(first) and _all_labeled_obj(params):
            reduce(produce, chain((first[1],), (f for _, f in params)))
            return Product(list(chain((first,), params)))

        raise ValueError("Missing param")

    return product
