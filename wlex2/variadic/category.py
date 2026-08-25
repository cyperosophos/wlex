from typing import Callable, Iterable, Iterator
from itertools import chain

from . import AdaptingMor, AdaptingComposable
from ..model.category import Obj, Mor, Composition
from ..model.lex import Equalizer
from ..proven import category
from ..trusted import category as pcategory
from . import it_with_first
from ..equality import Verifier
from .lex import lift

Composable = Iterable[Mor]

def compose(target: Obj, c: Composable, proofs: Verifier[object] | None = None) -> Mor:
    # Variadic normalized composition
    # There has to be a "straighten" method which makes mors match.
    res = pcategory.identity(target)
    for factor in c:
        # We compose left-associatively since it is the `factors` on the left
        # that gets reused.
        if isinstance(res, Composition):
            res.frozen = False

        if proofs is None:
            res = category.compose((res, factor))
        else:
            res = restricting_compose((res, factor), proofs)

    return res

def restricting_compose(factors: tuple[Mor, Mor], proofs: Verifier[object]) -> Mor:
    try:
        return category.compose(factors)
    except category.CompositionError:
        f, g = factors
        target = f.target

        # There is no way to handle the complementary case by lifting, since it requires
        # at least one requirement for type-checking.
        if isinstance(target, Equalizer):
            g = lift(g, , proofs, restrict=True)

# def with_source(mor: AdaptingMor, source: Obj):
#     if isinstance(mor, Callable):
#         return mor(source)

#     if mor.source != source:
#         raise ValueError("Source doesn't match.")

#     return mor

def adapting_compose(c: Iterable[AdaptingMor]) -> AdaptingMor:
    adapter = ComposeAdapter(c)
    f0, factors = it_with_first(adapter.composable())

    if f0 is None:
        def comp_only_pending(src: Obj):
            x0, f = it_with_first(adapter.flush(src))
            if x0 is None:
                raise ValueError("Empty factors")

            return compose(x0.target, f)

        return comp_only_pending

    comp = compose(f0.target, factors) # This consumes the factors iterator.
    if adapter.pending:
        def comp_with_pending(src: Obj):
            f = adapter.flush(src)
            return compose(comp.target, chain((comp,), f))

        return comp_with_pending

    return comp

class ComposeAdapter:
    __slots__ = ('pending', 'factors')
    pending: list[Callable[[Obj], Mor]]
    factors: AdaptingComposable

    def __init__(self, factors: AdaptingComposable):
        self.pending = []
        self.factors = iter(factors)

    def flush(self, source: Obj):
        res: list[Mor] = []
        for factor in reversed(self.pending):
            mor = factor(source)
            res.append(mor)
            source = mor.target

        del self.pending[:]
        return reversed(res)

    def composable(self) -> Iterator[Mor]:
        pending = self.pending
        for factor in self.factors:
            if isinstance(factor, Callable):
                pending.append(factor)
            else:
                src = factor.target
                yield from self.flush(src)
                yield factor
