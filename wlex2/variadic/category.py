from typing import Callable, Iterable, Iterator, TypeGuard
from itertools import chain

from . import Transform
from ..model.category import Obj, Mor
from ..model.cart import Product, Pairing
from ..model.lex import Equalizer, Lift
from ..proven import category
from ..trusted import category as pcategory
from . import resolve
from ..logos import Logos

LabeledMor = tuple[str, Mor] | Mor
CartMor = Mor | tuple[LabeledMor, ...]
LabeledTransform = tuple[str, Transform] | Transform
CartTransform = Transform | tuple[LabeledTransform, ...]
Composable = Iterable[CartMor]

# tuple[Transform, ...] must become Transform with the use of pairing,
# before it can be processed in the Adapter. However, since calling pairing
# is done inside compose, one may need to produce instead a callable that
# returns a CartMor. The source used as argument of this callable is "preliminary,"
# and in this case it may be a product inferred from a CartMor.
# Tuple within tuple is not allowed.

class Composer:
    #__slots__ = ('proofs',)
    __slots__ = ('pending', 'factors', 'logos')
    pending: list[Transform | tuple[LabeledTransform, ...]]
    factors: Iterable[CartTransform]
    logos: Logos

    def __init__(self, logos: Logos, factors: Iterable[CartTransform | Obj]):
        self.pending = []
        self.factors = (
            pcategory.identity(x) if isinstance(x, Obj) else x
            for x in factors
        )
        self.logos = logos

    def flush(self, source: Obj):
        res: list[CartMor] = []
        for factor in reversed(self.pending):
            if isinstance(factor, (Mor, Callable, str, int)):
                mor = resolve(factor, source)
                source = mor.target
            elif factor == ():
                mor = self.logos.terminal_mor(source)
                source = mor.target
            else:
                mor = tuple(
                    _resolve_labeled(f, source)
                    for f in factor
                )
                source = self._tuple_target(mor)

            res.append(mor)

        del self.pending[:]
        return reversed(res)

    def composable(self) -> Iterator[CartMor]:
        pending = self.pending
        for factor in self.factors:
            if factor == ():
                pending.append(factor)
            elif _is_cart_mor(factor):
                if isinstance(factor, tuple):
                    src = self._tuple_target(factor)
                else:
                    src = factor.target

                yield from self.flush(src)
                yield factor
            else:
                pending.append(factor)

    def _fit_factor(self, target: Obj, factor: Mor) -> Mor:
        # This gets called when `target` != `factor.target`
        # TODO: Support coproj for Coproduct
        # Make superobjects coincide
        if not isinstance(target, Equalizer):
            return factor.proj(target)

        # Restrict and lift
        return self.lift(
            factor.proj(target.sup),
            target,
        ).incl(target)

    def fit_factor(self, target: Obj, factor: CartMor) -> Mor:
        if isinstance(factor, Mor):
            return self._fit_factor(target, factor)

        if not isinstance(target, Product):
            raise ValueError('Target must be product')

        return self.pairing(factor, target)

    def _compose(self, c: Composable):
        for factor in c:
            res = factor
            break
        else:
            assert False

        if isinstance(res, tuple):
            res = self.pairing(res)

        for factor in c:
            res = category.compose((
                res,
                self.fit_factor(res.source, factor)
            ))

        return res


    def _tuple_target(self, factor: tuple[LabeledMor, ...]):
        # This is used when there is no target for passing to `variadic.pairing`.
        res = self.product(
            m.target
            if isinstance(m, Mor)
            else (m[0], m[1].target)
            for m in factor
        )
        return res

    def pairing(
        self, components: Iterable[LabeledMor],
        target: Product | None = None,
    ) -> Pairing:
        raise TypeError("Pairing not supported")

    def product(self, components: Iterable[tuple[str, Obj] | Obj]) -> Product:
        # See limit. This can be called outside the ctx of composition.
        raise TypeError("Product not supported")

    def lift(
        self, mor: Mor,
        target: Equalizer,
    ) -> Lift:
        raise TypeError("Lift not supported")

    def compose(self) -> Transform:
        factors = self.composable()
        if self.pending:
            def comp(src: Obj):
                return self._compose(chain(
                    factors,
                    self.flush(src),
                ))

            return comp

        return self._compose(factors)

# def compose(
#     logic: Logic,
#     target: Obj,
#     c: Composable,
# ) -> Mor:
#     # Variadic normalized composition
#     # There has to be a "straighten" method which makes mors match.
#     # TODO: Remove target arg and call to identity?
#     res = pcategory.identity(target)
#     for factor in c:
#         # We compose left-associatively since it is the `factors` on the left
#         # that gets reused.
#         res = category.compose((res, logic.fit_factor(res.source, factor)))
#         # if proofs is None:
#         #     res = category.compose((res, factor))
#         # else:
#         #     res = restricting_compose((res, factor), proofs)

#     return res

# def restricting_compose(factors: tuple[Mor, Mor], proofs: Verifier[object]) -> Mor:
#     try:
#         return category.compose(factors) # TODO: Just lift!
#     except category.CompositionError:
#         # TODO: Separate lifting
#         f, g = factors
#         target = f.target
#         g = lift(g, target, proofs, restrict=True)
#         #...

# def with_source(mor: AdaptingMor, source: Obj):
#     if isinstance(mor, Callable):
#         return mor(source)

#     if mor.source != source:
#         raise ValueError("Source doesn't match.")

#     return mor

# TODO: Just include this in a TComposer class?
# def full_compose(
#     logic: Logic,
#     c: Iterable[CartTransform | Obj],
# ) -> Transform:
#     adapter = _TComposer(logic, (
#         pcategory.identity(x) if isinstance(x, Obj) else x
#         for x in c
#     ))
#     f0, factors = it_with_first(adapter.composable())

#     if f0 is None:
#         def comp_only_pending(src: Obj):
#             x0, f = it_with_first(adapter.flush(src))
#             if x0 is None:
#                 raise ValueError("Empty factors")

#             if isinstance(x0, tuple):
#                 t = _tuple_target(logic, x0)
#             else:
#                 t = x0.target

#             return compose(logic, t, f)

#         return comp_only_pending

#     if isinstance(f0, tuple):
#         tgt = _tuple_target(logic, f0)
#     else:
#         tgt = f0.target

#     comp = compose(logic, tgt, factors) # This consumes the factors iterator.
#     if adapter.pending:
#         def comp_with_pending(src: Obj):
#             f = adapter.flush(src)
#             return compose(logic, comp.target, chain((comp,), f))

#         return comp_with_pending

#     return comp

# class _TComposer:
#     __slots__ = ('pending', 'factors', 'logic')
#     pending: list[Transform | tuple[LabeledTransform, ...]]
#     factors: Iterable[CartTransform]
#     logic: Logic

#     def __init__(self, logic: Logic, factors: Iterable[CartTransform]):
#         self.logic = logic
#         self.pending = []
#         self.factors = iter(factors)

#     def flush(self, source: Obj):
#         res: list[CartMor] = []
#         for factor in reversed(self.pending):
#             if isinstance(factor, (Mor, Callable, str, int)):
#                 mor = resolve(factor, source)
#                 source = mor.target
#             elif factor == ():
#                 mor = self.logic.terminal_mor(source)
#                 source = mor.target
#             else:
#                 mor = tuple(
#                     _resolve_labeled(f, source)
#                     for f in factor
#                 )
#                 source = _tuple_target(self.logic, mor)

#             res.append(mor)

#         del self.pending[:]
#         return reversed(res)

#     def composable(self) -> Iterator[CartMor]:
#         pending = self.pending
#         for factor in self.factors:
#             if factor == ():
#                 pending.append(factor)
#             elif _is_cart_mor(factor):
#                 if isinstance(factor, tuple):
#                     src = _tuple_target(self.logic, factor)
#                 else:
#                     src = factor.target

#                 yield from self.flush(src)
#                 yield factor
#             else:
#                 pending.append(factor)

def _is_cart_mor(
    f: CartTransform,
) -> TypeGuard[CartMor]:
    if isinstance(f, Mor):
        return True

    if isinstance(f, (Callable, str, int)):
        return False

    return all(
        isinstance(x, Mor) or (
            isinstance(x, tuple)
            and isinstance(x[1], Mor)
        ) for x in f
    )

def _resolve_labeled(t: LabeledTransform, source: Obj):
    if isinstance(t, (Mor, Callable, str, int)):
        return resolve(t, source)

    l, t = t
    return l, resolve(t, source)
