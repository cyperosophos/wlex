"""Private model of `cart` morphisms"""
from ..model import cart
from ..model.category import Obj, Mor
from .category import source, compose
from ..equality import Eq

NullParam = cart.NullParam
NullSpan = cart.BaseNullSpan

terminal = cart.Terminal
TerminalMor = Mor
terminal_mor = cart.TerminalMor

def _null_span(tm: TerminalMor) -> NullSpan:
    t = tm.target
    assert isinstance(t, cart.Terminal)
    return cart.NullSpan(source(tm), t.par)

def terminal_mor_hat(s: NullSpan):
    assert s == _null_span(terminal_mor(s))
    return Eq(s, s)

def terminal_mor_ihat(tm: TerminalMor):
    assert tm == terminal_mor(_null_span(tm))
    return Eq(tm, tm)

Param = cart.Param

def param_x(par: Param) -> Obj:
    return par.x

def param_y(par: Param) -> Obj:
    return par.y

Span = cart.BaseSpan
product = cart.Product

def product_hat(par: Param):
    assert par == product(par).par
    return Eq(par, par)

Pairing = Mor
pairing = cart.Pairing

def _span(pm: Pairing) -> Span:
    mor = pm
    # We rely on the double use of Product as the Span of projections,
    # so we don't create a new Product instance.
    t = mor.target
    assert isinstance(t, cart.Product)
    prod = product(t.par)
    return cart.Span(
        compose((prod.p(), mor)),
        compose((prod.q(), mor)),
        t.par,
    )

def pairing_hat(s: Span):
    assert s == _span(pairing(s))
    return Eq(s, s)

def pairing_ihat(pm: Pairing):
    # The pairing == span isomorphism proves the naturality of the diagonal.
    # One just needs to apply each projection.
    # (f, g) @ h -> ($0 @ (f, g) @ h, -> (f @ h,
    #                $1 @ (f, g) @ h)     g @ h)
    # Not every pairing here is an instance of cart.Pairing.

    return Eq(pm, pairing(_span(pm)))
