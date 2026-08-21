"""Private model of `cart` morphisms"""
from typing import Sequence

from ..model import cart
from .category import *

TerminalMor = Mor
LabeledObj = tuple[str, Obj] | Obj
Param = tuple[LabeledObj, LabeledObj]
Span = Sequence[Mor] # Length 2 (dynamic check >= 2 is implicit)
Pairing = cart.BasePairing # Length 2

def _remove_label(obj: LabeledObj):
    if isinstance(obj, tuple):
        return obj[1]

    return obj

def terminal() -> Obj:
    return cart.Product(())

def terminal_mor(obj: Obj) -> TerminalMor:
    return cart.Pairing(obj)

def terminal_mor_hat(obj: Obj):
    assert obj == source(terminal_mor(obj))
    return Eq(obj, obj)

def terminal_mor_ihat(tm: TerminalMor):
    assert tm == terminal_mor(source(tm))
    return Eq(tm, tm)

def param_x(par: Param) -> Obj:
    return _remove_label(par[0])

def param_y(par: Param) -> Obj:
    return _remove_label(par[1])

def product(par: Param) -> Span:
    return cart.Product(par)

def product_hat(par: Param):
    p, q = product(par)
    assert par == (target(p), target(q))
    return Eq(par, par)

def pairing(s: Span) -> Pairing:
    return cart.Pairing(s)

def _span(pm: Pairing) -> Span:
    x, y = pm
    mor = pm.mor
    p, q = product((x, y))
    return (
        compose((p, mor)),
        compose((q, mor)),
    )

def pairing_hat(s: Span):
    assert Span.__eq__(s, _span(pairing(s)))
    return Eq(s, s)

def pairing_ihat(pm: Pairing):
    # The pairing == span isomorphism proves the naturality of the diagonal.
    # One just needs to apply each projection.
    # (f, g) @ h -> ($0 @ (f, g) @ h, -> (f @ h,
    #                $1 @ (f, g) @ h)     g @ h)
    # Not every pairing here is an instance of cart.Pairing.

    return Eq(pm, pairing(_span(pm)))
