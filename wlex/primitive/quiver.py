from wlex.ambient.cells import (
    Obj, Mor, Eq,
)
from wlex.ambient.private import category

Node = Obj
Edge = Mor

def source(edge: object):
    assert isinstance(edge, Edge)
    return category.source(edge)

def target(edge: object):
    assert isinstance(edge, Edge)
    return category.target(edge)

Q1Edge = Eq

def Q1_source(edge: object):
    assert isinstance(edge, Q1Edge)
    return category.ssource(edge)

def Q1_target(edge: object):
    assert isinstance(edge, Q1Edge)
    return category.starget(edge)
