"""Public model of `category` morphisms"""
from ..trusted import category
from . import validated as v

def is_composable(c: category.Composable):
    f, g = c
    return source(f) == target(g)

def is_associativity_source(s: category.AssociativitySource):
    f, g, h = s
    return (
        is_composable((f, g))
        and is_composable((g, h))
    )

source = category.source
target = category.target
identity = category.identity
identity_hat = category.identity_hat
compose = v(category.compose, is_composable)
compose_hat = v(category.compose_hat, is_composable)
eq_left_identity_law = category.eq_left_identity_law
eq_right_identity_law = category.eq_right_identity_law
eq_associativity = category.eq_associativity

# === is for "private equalities", equality of elements
# equalities of morphisms produce equalities of elements.
# One does not need a different Eq class.
# Eq is the fundamental class of the (meta)theory of sets.
# The fact that one has to verify equalities at the public
# interface corresponds to the shortcoming of Python's
# static typing. These are still equalities of elements.
# The equalities of morphisms (elements of (meta) Mor)
# get checked during compilation.
