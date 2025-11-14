"""Private model of `cart` morphisms"""
from ..private import cart
from ..cells import Mor, Eq
from . import validate

TerminalMor = cart.TerminalMor
ObjObj = cart.ObjObj
Span = cart.Span
ProductMor = cart.ProductMor
SpanEq = cart.SpanEq

terminal = cart.terminal
terminal_mor = cart.terminal_mor

def terminal_mor_unique(mor: cart.TerminalMor) -> Eq:
    """Public model of equality `cart.terminal_mor_unique`"""
    validate(mor, cart.is_terminal_mor)
    return cart.terminal_mor_unique(mor)

product = cart.product

def pairing(s: cart.Span) -> cart.ProductMor:
    """Public model of morphism `cart.pairing`"""
    validate(s, cart.is_span)
    return cart.pairing(s)

def pairing_unique(pm: cart.ProductMor) -> Eq:
    """Private model of morphism `cart.pairing_unique`"""
    validate(pm, cart.is_product_mor)
    return cart.pairing_unique(pm)
