"""Private model of `category` morphisms"""
from ..model.category import Obj, Mor, Composition
from ..equality import Eq

def source(mor: Mor) -> Obj:
    return mor.source

def target(mor: Mor) -> Obj:
    return mor.target

def identity(obj: Obj) -> Mor:
    return Composition(obj)

Composable = tuple[Mor, Mor]

def identity_hat(obj: Obj):
    i = identity(obj)
    s = (
        obj, obj,
    )
    assert s == (
        source(i),
        target(i),
    )
    return Eq(s, s)

def compose(c: Composable) -> Mor:
    return Composition.strict(*c)

def compose_hat(c: Composable):
    h = compose(c)
    f, g = c
    s = (
        source(g),
        target(f),
    )
    assert s == (
        source(h),
        target(h),
    )
    return Eq(s, s)

def eq_left_identity_law(mor: Mor):
    assert compose((identity(target(mor)), mor)) == mor
    return Eq(mor, mor)

def eq_right_identity_law(mor: Mor):
    assert compose((mor, identity(source(mor)))) == mor
    return Eq(mor, mor)

_AssociativitySource = tuple[Mor, Mor, Mor]

def eq_associativity(c: _AssociativitySource):
    f, g, h = c
    mor = compose((compose((f, g)), h))
    assert compose((f, compose((g, h)))) == mor
    return Eq(mor, mor)
