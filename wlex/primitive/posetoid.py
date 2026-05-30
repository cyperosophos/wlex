from typing import TypedDict, TypeGuard

from wlex.ambient.cells import (
    Obj, Mor, Eq,
)
from wlex.ambient.private import category

from . import quiver

El = quiver.Edge
Rel = quiver.Q1Edge
source = quiver.Q1_source
target = quiver.Q1_target

Path = TypedDict('Path', {'f': Rel, 'g': Rel})
def _is_path(path: object) -> TypeGuard[Path]:
    return (
        isinstance(path, dict)
        and isinstance(path['f'], Rel)
        and isinstance(path['g'], Rel)
    )

def ref(el: object):
    assert isinstance(el, El)
    return category.ref(el)

def trans(path: object):
    assert _is_path(path)
    return category.trans((path['f'], path['g']))

Eq = Rel

def sym(eq: object):
    assert isinstance(eq, Eq)
    return category.sym(eq)

EqUniqueSource = TypedDict('EqUniqueSource', {'d': Eq, 'e': Eq})
def _is_eq_unique_source(s: object) -> TypeGuard[EqUniqueSource]:
    return (
        isinstance(s, dict)
        and isinstance(s['d'], Eq)
        and isinstance(s['e'], Eq)
    )

# TODO: Check that hat peak can be adapted to having the reqs.
def eq_unique(s: object):
    assert _is_eq_unique_source(s)
    return category.eq_unique((s['d'], s['e']))
