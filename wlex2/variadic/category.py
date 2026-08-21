from typing import Callable, Iterable, Iterator
from itertools import chain

from ..model.category import Obj, Mor, Composition
from ..proven import category
from ..trusted import category as pcategory

Composable = Iterable[Mor]

def compose(target: Obj, c: Composable) -> Mor:
    # Variadic normalized composition
    # There has to be a "straighten" method with makes mors match.
    res = pcategory.identity(target)
    for factor in c:
        # We compose left-associatively since it is the `factors` on the left
        # that gets reused.
        if isinstance(res, Composition):
            res.frozen = False

        res = category.compose((res, factor))

    return res

AdaptingMor = Mor | Callable[[Obj], Mor]
AdaptingComposable = Iterable[AdaptingMor]

def adapting_compose(c: AdaptingComposable, source: Obj | None = None) -> AdaptingMor:
    adapter = ComposableAdapter(c)
    target, factors = adapter.composable(source)

    if target is None:
        def comp_only_pending(src: Obj):
            t, factors = adapter.composable(src)
            if t is None:
                raise ValueError("Empty factors")

            return compose(t, factors)

        return comp_only_pending

    comp = compose(target, factors) # The consumes the factors iterator.
    if adapter.pending:
        def comp_with_pending(src: Obj):
            t, factors = adapter.composable(src)
            assert t
            return compose(comp.target, chain((comp,), factors))

        return comp_with_pending

    return comp

class ComposableAdapter:
    __slots__ = ('pending', 'target', 'factors')
    pending: list[Callable[[Obj], Mor]]
    target: Obj
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

    def _composable(self, source: Obj | None) -> Iterator[Mor]:
        pending = self.pending
        for factor in self.factors:
            if isinstance(factor, Callable):
                pending.append(factor)
            else:
                src = factor.target
                yield from self.flush(src)
                yield factor

        if source:
            yield from self.flush(source)

    def composable(self, source: Obj | None):
        it = self._composable(source)
        for factor in it:
            self.target = factor.target
            break
        else:
            return None, it

        return self.target, chain((factor,), it)
