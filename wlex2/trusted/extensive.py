"""Private model of `extensive` morphisms"""
from typing import Sequence

from ..model import extensive
from ..model.category import Mor, Parallel
from .category import source, compose
from .cart import terminal, terminal_mor
from .lex import equalizer
from ..equality import Eq

Cospan = Sequence[Mor]
Copairing = Mor
Selector = Mor

coproduct = extensive.Coproduct

# TODO: Fix return types in rest of `trusted`
def copairing(cs: Cospan) -> extensive.Copairing:
    p, q = cs
    coprod = coproduct((source(p), source(q)))
    return extensive.Copairing(cs, coprod)

def _cospan(cp: Copairing) -> Cospan:
    mor = cp
    src = mor.source
    assert isinstance(src, extensive.Coproduct)
    p, q = src
    return (
        compose((mor, p)),
        compose((mor, q)),
    )

def copairing_hat(cs: Cospan):
    assert Cospan.__eq__(cs, _cospan(copairing(cs)))
    return Eq(cs, cs)

def copairing_ihat(cp: Copairing):
    return Eq(cp, copairing(_cospan(cp)))

def bool_() -> extensive.Coproduct:
    return coproduct((terminal(), terminal()))

# def case(sel: Selector) -> Parallel:
#     src = source(sel)
#     return Parallel(src, ((
#         sel,
#         compose((bool_()[0], terminal_mor(src))),
#     ),))

# def case_hat(sel: Selector):
#     assert sel == case(sel)[0][0]
#     return Eq(sel, sel)

def case_target(sel: Selector):
    ((i, j),) = case(sel)
    assert j == compose((bool_()[0], terminal_mor(source(i))))
    return Eq(j, j)

def select(sel: Selector) -> Mor:
    return equalizer(case(sel)).mor()

# def negation() -> extensive.Copairing:
#     p, q = bool_()
#     return copairing((q, p))

def stick(sel: Selector) -> Mor:
    return copairing((
        select(sel),
        select(compose((negation(), sel))),
    ))

def split(sel: Selector) -> Mor:
    return

# The isos equalities cannot fully rely on `reduce`. They need
# a proof of isomorphism of equalizers (the one based on negation,
# the other based on the false arrow).
