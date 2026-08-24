from ..trusted import cart
from . import validated as v, ValidationError
from .category import *

def is_terminal_mor(tm: cart.TerminalMor):
    if target(tm) == terminal():
        return

    raise ValidationError("Invalid")

def is_span(sp: cart.Span):
    p, q = sp
    x, y = sp.param()
    if (
        source(p) == source(q)
        and x == target(p)
        and y == target(q)
    ):
        return

    raise ValidationError("Invalid")

def is_pairing(p: cart.Pairing):
    # Initialization checks should be minimal so as to not unnecessarily impact performance.
    # Checks are better done in `proven` (public interface).
    # `target(p.mor) == product(p.param())`
    # Is given by the definition of `param` which is a retraction of `product`.
    if len(p) == 2:
        return

    raise ValidationError("Invalid")

terminal = cart.terminal
terminal_mor = cart.terminal_mor
terminal_mor_hat = cart.terminal_mor_hat
terminal_mor_ihat = v(cart.terminal_mor_ihat, is_terminal_mor)
param_x = cart.param_x
param_y = cart.param_y
product = cart.product
product_hat = cart.product_hat
pairing = v(cart.pairing, is_span)
pairing_hat = v(cart.pairing_hat, is_span)
pairing_ihat = v(cart.pairing_ihat, is_pairing)
