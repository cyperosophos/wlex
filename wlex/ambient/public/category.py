"""Public model of `category` morphisms

Here public means that there is dynamic validation (type checking) of arguments
besides the static type checking supported through type annotations.
"""
from ..private import category
from ..cells import Mor, Eq
from . import validate

source = category.source
target = category.target

def compose(c: category.Composable) -> Mor:
    """Public model of morphism `category.compose`"""
    validate(c, category.is_composable)
    return category.compose(c)

identity = category.identity

def ssource(eq: Eq) -> Mor:
    """Public model of morphism `category.S.source`"""
    validate(eq, category.is_eq)
    return category.ssource(eq)

def starget(eq: Eq) -> Mor:
    """Public model of morphism `category.S.target`"""
    validate(eq, category.is_eq)
    return category.starget(eq)

ref = category.ref

def trans(p: category.Path) -> Eq:
    """Public model of morphism `category.trans`"""
    validate(p, category.is_path)
    return category.trans(p)

left_identity_law = category.left_identity_law
right_identity_law = category.right_identity_law

def associativity(s: category.AssociativitySource) -> Eq:
    """Public model of morphism `category.associativity`"""
    validate(s, category.is_associativity_source)
    return category.associativity(s)

def eq_signature(eq: Eq):
    """Public model of morphism `category.S.eq`"""
    validate(eq, category.is_eq)
    return category.eq_signature(eq)

def eq_unique(s: category.EqUniqueSource):
    """Public model of morphism `category.S.unique`"""
    validate(s, category.is_path)
    return category.eq_unique(s)

def sym(eq: Eq):
    """Public model of morphism `category.S.S.sym`"""
    validate(eq, category.is_eq)
    return category.sym(eq)

def compose_eq(c: category.ComposableEq):
    """Public model of morphism `category.compose_eq`"""
    validate(c, category.is_composable_eq)
    return category.compose_eq(c)
