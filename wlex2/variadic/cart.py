from typing import Iterable, TypeGuard

from ..model.category import Obj, Param
from ..proven import cart
from ..trusted import cart as pcart
from ..model.cart import Pairing, Product, Span as ConcreteSpan
from . import it_with_first
from .category import *

Span = pcart.Span

def product(components: Iterable[tuple[str, Obj] | Obj]) -> Span:
    res = pcart.terminal()
    assert isinstance(res, Product)
    for component in components:
        res.frozen = False
        res = cart.product(Param((res, component)))
        assert isinstance(res, Product)

    return res

def _component_target(component: tuple[str, Mor] | Mor):
    if isinstance(component, tuple):
        l, c = component
        return l, c.target

    return component.target

def _no_label(component: tuple[str, Mor] | Mor):
    if isinstance(component, tuple):
        return component[1]

    return component

def _no_empty_label(component: tuple[str, Mor]):
    l, c = component
    if l:
        return component

    return c

def pairing(source: Obj, components: Iterable[tuple[str, Mor] | Mor]) -> Pairing:
    # Composition straightening corrects the order of components based on the
    # desirable target.
    res = pcart.terminal_mor(source)
    target = res.target
    assert isinstance(res, Pairing)
    assert isinstance(target, Product)
    for component in components:
        res.frozen = False
        target.frozen = False
        res = cart.pairing(ConcreteSpan(
            (res, _no_label(component)),
            Param((target, _component_target(component))),
        ))
        assert isinstance(res, Pairing)
        target = res.target
        assert isinstance(target, Product)

    return res

# def _span(pm: BasePairing) -> Span:
#     mor = pm.mor
#     pspan = mor.target
#     assert isinstance(pspan, Product)
#     return ConcreteSpan((
#         pcart.compose((p, pm.mor)) for p in pspan
#     ), pm.param())

# def pairing_ihat(pm: BasePairing):
#     # No requirement type-checking needed on Pairing
#     # We assume the proof.
#     return Eq(
#         pm,
#         pairing(_span(pm)),
#     )

AdaptingComponent = tuple[str, AdaptingMor] | AdaptingMor
AdaptingComponents = Iterable[AdaptingComponent]

def adapting_pairing(*c: AdaptingComponent) -> AdaptingMor:
    # Source gets inferred from precomposed factor only after trying all
    # cmponents.
    adapter = PairingAdapter(c)
    c0, components = it_with_first(adapter.components())

    if c0 is None:
        def pair_only_pending(src: Obj):
            comp = adapter.flush(src)
            return pairing(src, comp)

        return pair_only_pending

    # Either all components are pending or none are.
    return pairing(_no_label(c0).source, components)

class PairingAdapter:
    __slots__ = ('pending', '_components')
    pending: list[tuple[str, Callable[[Obj], Mor]]]
    _components: AdaptingComponents

    def __init__(self, components: AdaptingComponents):
        self.pending = []
        self._components = iter(components)

    def flush(self, source: Obj):
        for label, component in self.pending:
            yield _no_empty_label((label, component(source)))

        del self.pending[:]

    def components(self) -> Iterator[tuple[str, Mor] | Mor]:
        def _is_labeled_component(c: AdaptingComponent) -> TypeGuard[tuple[str, AdaptingMor]]:
            return isinstance(c, tuple)

        pending = self.pending
        for component in self._components:
            if _is_labeled_component(component):
                label, component = component
            else:
                label = ''

            if isinstance(component, Callable):
                pending.append((label, component))
            else:
                assert isinstance(component, Mor)
                src = component.source
                yield from self.flush(src)
                yield _no_empty_label((label, component))
                for c in self._components:
                    if _is_labeled_component(c):
                        l, c = c
                    else:
                        l = ''

                    if isinstance(c, Callable):
                        yield _no_empty_label((l, c(src)))
                    else:
                        assert isinstance(c, Mor)
                        yield _no_empty_label((l, c))

def proj(label: str | int):
    def fn(src: Obj):
        if not isinstance(src, Product):
            raise ValueError('Source must be product.')

        if isinstance(label, str):
            l = src.label_to_idx(label)
        else:
            l = label

        return src[l]

    return fn

def prod(*components: tuple[str, Obj] | Obj):
    res = product(components)
    assert isinstance(res, Obj)
    return res