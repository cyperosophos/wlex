"""Private model of `cart` morphisms"""
from ..model import cart
from ..model.category import Param
from .category import *

TerminalMor = Mor
Span = cart.BaseSpan # Length 2 (dynamic check >= 2 is implicit)
Pairing = Mor # Length 2

def terminal() -> Obj:
    return cart.Product(Param(()))

def terminal_mor(obj: Obj) -> TerminalMor:
    return cart.Pairing(obj, cart.Product(Param(())))

def terminal_mor_hat(obj: Obj):
    assert obj == source(terminal_mor(obj))
    return Eq(obj, obj)

def terminal_mor_ihat(tm: TerminalMor):
    assert tm == terminal_mor(source(tm))
    return Eq(tm, tm)

def param_x(par: Param) -> Obj:
    return par[0]

def param_y(par: Param) -> Obj:
    return par[1]

product = cart.Product

def product_hat(par: Param):
    p, q = product(par)
    assert par == (target(p), target(q))
    return Eq(par, par)

def pairing(s: Span) -> Pairing:
    prod = product(s.param())
    return cart.Pairing(s, prod)

def _span(pm: Pairing) -> Span:
    mor = pm
    # We use the double use of Product as the Span of projections,
    # so we don't create a new Product instance.
    tgt = mor.target
    assert isinstance(tgt, cart.Product)
    p, q = tgt
    return cart.Span((
        compose((p, mor)),
        compose((q, mor)),
    ), pm.target.param().labels())

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
