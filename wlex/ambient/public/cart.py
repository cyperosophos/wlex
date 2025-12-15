"""Public model of `cart` morphisms"""
from ..private import cart
from . import validated

terminal = cart.terminal
terminal_mor = cart.terminal_mor
terminal_mor_unique = validated(cart.terminal_mor_unique, cart.is_terminal_mor)
product = cart.product
pairing = validated(cart.pairing, cart.is_span)
pairing_unique = validated(cart.pairing_unique, cart.is_product_mor)
pairing_eq = validated(cart.pairing_eq, cart.is_span_eq)
