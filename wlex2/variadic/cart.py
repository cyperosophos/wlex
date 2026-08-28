from typing import Iterable, Callable, Sequence
from itertools import chain

from ..model.category import Obj, Mor, Param
from ..model.lex import Equalizer
from ..proven import cart, ValidationError
from ..trusted import cart as pcart
from ..model.cart import Pairing, Product, Span as ConcreteSpan
from . import it_with_first

Span = pcart.Span

def product(components: Iterable[tuple[str, Obj] | Obj]) -> Product:
    res = pcart.terminal()
    assert isinstance(res, Product)
    for component in components:
        res.frozen = False
        res = cart.product(Param((res, component)))
        assert isinstance(res, Product)

    return res

# def _component_target(component: tuple[str, Mor] | Mor):
#     if isinstance(component, tuple):
#         l, c = component
#         return l, c.target

#     return component.target

def _no_label(component: tuple[str, Mor] | Mor):
    if isinstance(component, tuple):
        return component[1]

    return component

# def _no_empty_label(component: tuple[str, Mor]):
#     l, c = component
#     if l:
#         return component

#     return c

def _intersection(x: Obj, y: Obj):
    # Return the smallest object along with all requirements from both objects.
    if isinstance(x, Equalizer):
        if isinstance(y, Equalizer):
            if x.sup != y.sup:
                raise ValidationError("Can't intersect")

            reqs = chain(x.requirements, y.requirements)
            if len(x.requirements) < len(y.requirements):
                return y, reqs

            return x, reqs

        if x.sup != y:
            raise ValidationError("Can't intersect")

        return x, x.requirements

    if isinstance(y, Equalizer):
        if x != y.sup:
            raise ValidationError("Can't intersect")

        return y, y.requirements

    if x != y:
        raise ValidationError("Can't intersect")

    return x, ()

def _fit_list(
    components: Sequence[Obj],
    it: Iterable[tuple[str, Mor]],
    fit: Callable[[Obj, Mor], Mor],
    eqr: Callable[[Obj, Iterable[tuple[Mor, Mor]]], Obj],
):
    res: list[tuple[str, Mor]] = []
    for i, (l, c) in enumerate(it):
        c = fit(components[i], c)
        res.append((l, c))

    # for i, (l, c) in enumerate(it):
    #     # TODO: Type checking needed!! Use proven.compose instead of restrict?
    #     res[i] = (l, src.restrict(c))

    # Cf. Parallel.is_valid
    # We use an ad-hoc intersection instead lifting identities because the point
    # here is to construct valid arguments for `pairing`.
    res_it = iter(res)
    reqs: set[tuple[Mor, Mor]] = set()
    for _, c in res_it:
        src = c.source
        break
    else:
        assert False

    for _, c in res_it:
        src, r = _intersection(src, c.source)
        reqs.update(r)

    # Can't rely on variadic equalizer for all the necessary type-checking
    # hence _intersection must do type-checking.
    common_src = eqr(src, reqs)
    for i, (l, m) in enumerate(res):
        res[i] = (l, common_src.restrict(m))

    return res

#def pairing(source: Obj, components: Iterable[tuple[str, Mor] | Mor]) -> Pairing:
def pairing(
    components: Iterable[tuple[str, Mor] | Mor],
    target: Product,
    #restrict_source: bool = False, # This will just shrink the source to an intersection.
    fit: Callable[[Obj, Mor], Mor],
    eqr: Callable[[Obj, Iterable[tuple[Mor, Mor]]], Obj],
) -> Pairing:
    # The target will get reconstructed. Cf. lift.
    # Components can have labels, so that they get rearranged based on target.
    first, it = it_with_first(iter(components))
    if not first:
        raise ValueError("Empty components")

    source = _no_label(first).source
    res = pcart.terminal_mor(source)
    mtarget = res.target
    assert isinstance(res, Pairing)
    assert isinstance(mtarget, Product)
    for label, component in _fit_list(
        target.components,
        target.pairing_components(it),
        fit, eqr,
    ):
        # TODO: One still needs to check that the component target and the target component
        # coincide. It seems one should support lifting/restricting at this point.
        # (See old code regarding product of equalizers being the equalizer of a product.
        # Applying this for normalization seems to overcomplicate the pairing of morphisms
        # with equalizers as targets.)
        # In variadic.lift, ConcreteFork has an implicit check of target matching
        # up to inclusion. We need this check here.
        # There is a difference with variadic.lift. If we leave out (exact) target matching,
        # we can still have it when type-checking the composition, whereas with lifting
        # composition already assumes that lifting takes care of target matching since it is
        # an operation carried out from within high-level composition. Hence it only makes
        # sense to match targets here by doing lifting/restricting (not just inclusion).
        # The conclusion is that pairing must be handled by composition the way lift is
        # Instead of p(f, g), one would write c((f, g)), etc.

        res.frozen = False
        mtarget.frozen = False
        res = cart.pairing(ConcreteSpan(
            (res, component),
            ('', label),
        ))
        assert isinstance(res, Pairing)
        mtarget = res.target
        assert isinstance(mtarget, Product)

    # We leave it to `compose` to check that `res.target` is `target`.
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

# AdaptingComponent = tuple[str, Transform] | Transform
# AdaptingComponents = Iterable[AdaptingComponent]

# def adapting_pairing(*c: AdaptingComponent) -> Transform:
#     # Source gets inferred from precomposed factor only after trying all
#     # cmponents.
#     adapter = PairingAdapter(c)
#     c0, components = it_with_first(adapter.components())

#     if c0 is None:
#         def pair_only_pending(src: Obj):
#             comp = adapter.flush(src)
#             return pairing(src, comp)

#         return pair_only_pending

#     # Either all components are pending or none are.
#     return pairing(_no_label(c0).source, components)

# class PairingAdapter:
#     __slots__ = ('pending', '_components')
#     pending: list[tuple[str, Callable[[Obj], Mor]]]
#     _components: AdaptingComponents

#     def __init__(self, components: AdaptingComponents):
#         self.pending = []
#         self._components = iter(components)

#     def flush(self, source: Obj):
#         for label, component in self.pending:
#             yield _no_empty_label((label, component(source)))

#         del self.pending[:]

#     def components(self) -> Iterator[tuple[str, Mor] | Mor]:
#         def _is_labeled_component(c: AdaptingComponent) -> TypeGuard[tuple[str, Transform]]:
#             return isinstance(c, tuple)

#         pending = self.pending
#         for component in self._components:
#             if _is_labeled_component(component):
#                 label, component = component
#             else:
#                 label = ''

#             if isinstance(component, Callable):
#                 pending.append((label, component))
#             else:
#                 assert isinstance(component, Mor)
#                 src = component.source
#                 yield from self.flush(src)
#                 yield _no_empty_label((label, component))
#                 for c in self._components:
#                     if _is_labeled_component(c):
#                         l, c = c
#                     else:
#                         l = ''

#                     if isinstance(c, Callable):
#                         yield _no_empty_label((l, c(src)))
#                     else:
#                         assert isinstance(c, Mor)
#                         yield _no_empty_label((l, c))
