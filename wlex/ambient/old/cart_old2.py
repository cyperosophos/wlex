"""High level interface for cartesian ambient"""
from collections.abc import Sequence, Iterator
from typing import TypeGuard, overload
from itertools import chain

from .cells import Obj, Mor, Eq
from . import category
from .category import EqLike, MorLike, Transformation, Law, reduce
from .public import cart as public
from .cells.cart import ProductMor

class CartContext(category.Context):
    """Handles cells of a theory with ambient cart"""
    __slots__ = ()

    terminal = staticmethod(public.terminal)
    product = staticmethod(public.product)
    pairing = staticmethod(public.pairing)
    pairing_eq = staticmethod(public.pairing_eq)

    @staticmethod
    def proj(name: str | int):
        """Create projection transformation from name"""
        @Transformation
        def _proj(source: Obj):
            return source.proj(name)

        return _proj

    def el(self, name: str, cell: MorLike, target: Obj | None = None):
        """Sets name on element and checks its type

        An element is a morphism from the terminal object.
        """
        return self.mor(
            name, cell,
            target and (self.terminal(type(target)), target),
        )

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
    ) -> Eq | Law:
        return _pairing_eq(self._pair_eq, first, factors)

    @overload
    def pair(
        self,
        first: tuple[str | int, MorLike],
        *factors: tuple[str | int, MorLike],
    ) -> Mor | Transformation: ...
    @overload
    def pair(
        self,
        first: tuple[str | int, Eq | Law],
        *factors: tuple[str | int, EqLike],
    ) -> Eq | Law: ...
    @overload
    def pair(
        self,
        first: tuple[str | int, MorLike],
        *factors: tuple[str | int, Eq | Law],
    ) -> Eq | Law: ...

    def pair(
        self,
        first: tuple[str | int, EqLike],
        *factors: tuple[str | int, EqLike],
    ) -> Mor | Transformation | Eq | Law:
        """Variadic high-level pairing"""
        # A consistent even if somewhat cumbersome way of providing factors
        # (namely as tuples containing the label and the factor) makes sense,
        # since theories written in python are just transpilations of wlex.
        if not factors:
            raise ValueError("At least two components must be provided.")

        res = category.operate_mor_or_eq(
            self._pair_op_mor, self._pair_op_eq, first[1], [f for _, f in factors],
        )

        if isinstance(res, Mor):
            return _labeled_product_mor(res, factors)

        if isinstance(res, Transformation):
            @Transformation
            def _pair(source: Obj):
                return _labeled_product_mor(res(source), factors)

            return _pair

        if isinstance(res, Law):
            @Law
            def _pair_eq(source: Obj):
                e = res(source)
                eq = Eq(
                    _labeled_product_mor(e.ssource, factors),
                    _labeled_product_mor(e.starget, factors),
                )
                eq.proven = e.proven
                return eq

            return _pair_eq

        eq = Eq(
            _labeled_product_mor(res.ssource, factors),
            _labeled_product_mor(res.starget, factors),
        )
        eq.proven = res.proven
        return eq

    def _produce(self, objs: tuple[Obj, Obj]):
        return self.product(objs)[0].source

    def prod(self, first: tuple[str | int, Obj], *params: tuple[str | int, Obj]) -> Obj:
        """Variadic high-level products"""
        reduce(self._produce, chain((first[1],), (f for _, f in params)))
        res = first[1].vproduct(list(chain((first,), params)))
        return res

    def weak(self, mor: Mor):
        """Make transformation out of morphism to allow weakening"""
        @Transformation
        def _t(source: Obj):
            return mor.compose(self.proj(mor.source)(source))

        return _t

def _unlabeled[T](factors: Iterator[T]) -> Sequence[tuple[str | int, T]]:
    return [('', f) for f in factors]

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
) -> Eq | Law:
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
    return res.source.vproduct_mor(_unlabeled(iter(args)), flattened=False)

def _eq_pairing(comp: category.Composer[Eq], factors: Iterator[Eq]):
    args = list(factors)
    res = reduce(comp, iter(args))
    source = res.ssource.source
    return Eq(
        source.vproduct_mor(_unlabeled(f.ssource for f in args)),
        source.vproduct_mor(_unlabeled(f.starget for f in args)),
    )

def _labeled_product_mor(
    unlabeled: Mor, labeled_params: Sequence[tuple[str | int, object]],
):
    assert isinstance(unlabeled, ProductMor)
    assert len(labeled_params) == len(unlabeled.components)
    return unlabeled.source.vproduct_mor([
        (label, component)
        for (label, _), (_, component)
        in zip(labeled_params, unlabeled.components.items())
    ])

def _all_eq(factors: Sequence[EqLike]) -> TypeGuard[Sequence[Eq]]:
    return all(isinstance(f, Eq) for f in factors)
