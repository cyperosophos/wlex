from ..model.category import Obj
from ..proven import cart
from ..trusted import cart as pcart
from ..model.cart import Pairing, Product, BasePairing, Components
from ..equality import Eq
from .category import *

Param = Components[Obj]
Span = pcart.Span

def product(par: Param) -> Span:
    res = pcart.terminal()
    assert isinstance(res, Product)
    for component in par:
        res.frozen = False
        res = cart.product((res, component))
        assert isinstance(res, Product)

    return res

def pairing(s: Span) -> Pairing:
    # TODO: Span should also be labeled? Should one modify the type in `lang`?
    # Composition straightening corrects the order of components based on the
    # desirable target. Labeling is required for the isomorphism, otherwise some
    # pairings would not have preimage.
    components = s
    res = pcart.terminal_mor(pcart.source(components[0]))
    assert isinstance(res, Pairing)
    for component in components:
        res.frozen = False
        res = cart.pairing((res, component))
        assert isinstance(res, Pairing)

    return res

def _span(pm: BasePairing) -> Span:
    pspan = product(pm)
    return [pcart.compose((p, pm.mor)) for p in pspan]

def pairing_ihat(pm: BasePairing):
    # No requirement type-checking needed on Pairing
    # We assume the proof.
    return Eq(
        pm,
        pairing(_span(pm)),
    )

# LabeledObjObj = Sequence[tuple[str, Obj] | Obj]

# def labeled_product(xy: LabeledObjObj):
#     labels, comps = Product.extract_labels(xy)
#     res = product(comps)
#     assert isinstance(res, Product)
#     res.set_labels(labels)
#     return res

# TODO: def adapting_pairing()
