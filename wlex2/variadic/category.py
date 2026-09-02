from typing import Callable, Iterable, Iterator, TypeGuard
from itertools import chain

from . import Transform
from ..model.category import Obj, Mor
from ..proven import category
from ..trusted import category as pcategory
from . import it_with_first, resolve
from .cart import product

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

def compose(
    target: Obj,
    c: Composable,
    #proofs: Verifier[object] | None = None,
    fit: Callable[[Obj, CartMor], Mor],
) -> Mor:
    # Variadic normalized composition
    # There has to be a "straighten" method which makes mors match.
    # TODO: Remove target arg and call to identity?
    res = pcategory.identity(target)
    for factor in c:
        # We compose left-associatively since it is the `factors` on the left
        # that gets reused.
        category.compose((res, fit(res.source, factor)))
        # if proofs is None:
        #     res = category.compose((res, factor))
        # else:
        #     res = restricting_compose((res, factor), proofs)

    return res

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

def tcompose(
    c: Iterable[CartTransform | Obj],
    fit: Callable[[Obj, CartMor], Mor],
    terminal_mor: Callable[[Obj], Mor],
) -> Transform:
    adapter = _TComposer((
        pcategory.identity(x) if isinstance(x, Obj) else x
        for x in c
    ), terminal_mor)
    f0, factors = it_with_first(adapter.composable())

    if f0 is None:
        def comp_only_pending(src: Obj):
            x0, f = it_with_first(adapter.flush(src))
            if x0 is None:
                raise ValueError("Empty factors")

            if isinstance(x0, tuple):
                t = _tuple_target(x0)
            else:
                t = x0.target

            return compose(t, f, fit)

        return comp_only_pending

    if isinstance(f0, tuple):
        tgt = _tuple_target(f0)
    else:
        tgt = f0.target

    comp = compose(tgt, factors, fit) # This consumes the factors iterator.
    if adapter.pending:
        def comp_with_pending(src: Obj):
            f = adapter.flush(src)
            return compose(comp.target, chain((comp,), f), fit)

        return comp_with_pending

    return comp

class _TComposer:
    __slots__ = ('pending', 'factors', 'terminal_mor')
    pending: list[Transform | tuple[LabeledTransform, ...]]
    factors: Iterable[CartTransform]
    terminal_mor: Callable[[Obj], Mor]

    def __init__(self, factors: Iterable[CartTransform], terminal_mor: Callable[[Obj], Mor]):
        self.pending = []
        self.factors = iter(factors)
        self.terminal_mor = terminal_mor

    def flush(self, source: Obj):
        res: list[CartMor] = []
        for factor in reversed(self.pending):
            if isinstance(factor, (Mor, Callable, str, int)):
                mor = resolve(factor, source)
                source = mor.target
            elif factor == ():
                mor = self.terminal_mor(source)
                source = mor.target
            else:
                mor = tuple(
                    _resolve_labeled(f, source)
                    for f in factor
                )
                source = _tuple_target(mor)

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
                    src = _tuple_target(factor)
                else:
                    src = factor.target

                yield from self.flush(src)
                yield factor
            else:
                pending.append(factor)

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

def _tuple_target(factor: tuple[LabeledMor, ...]):
    res = product(
        m.target
        if isinstance(m, Mor)
        else (m[0], m[1].target)
        for m in factor
    )
    return res

def _resolve_labeled(t: LabeledTransform, source: Obj):
    if isinstance(t, (Mor, Callable, str, int)):
        return resolve(t, source)

    l, t = t
    return l, resolve(t, source)
