from ..trusted import cart
from . import validated as v
from .category import *

def is_terminal_mor(tm: cart.TerminalMor):
    return target(tm) == terminal()

def is_span(sp: cart.Span):
    p, q = sp
    return source(p) == source(q)

def is_pairing(p: cart.Pairing):
    x, y = p
    return target(p.mor) == source(product((x, y))[0])

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
