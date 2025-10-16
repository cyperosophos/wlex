from ..static.category import *
from . import require

_compose = compose
_trans = trans
_eq_unique = eq_unique
_associativity = associativity
_compose_eq = compose_eq

def valid_composable(c: Composable):
    f, g = c
    # No check_eql here since at this level the type of source is Obj
    # not some instance of Obj (like when using backend).
    # The equiv comparison should not be modified to handle weakening
    # since conversion may be required anyway, and the comparison would
    # not be symmetric.
    return f.source.equiv(g.target)

def valid_path(p: Path):
    f, g = p
    # TODO: Wrap ssource and starget so that the comparison gets
    # actually done with ssource and ssource, etc., that is sym
    # equivalence is taken into account.
    return f.ssource.eql(g.starget)

def valid_eq_unique_source(s: EqUniqueSource):
    d, e = s
    return (
        d.ssource.eql(e.ssource)
        and d.starget.eql(e.starget)
    )

def valid_associativity_source(s: AssociativitySource):
    f, g, h = s
    return (
        valid_composable((f, g))
        and valid_composable((g, h))
    )

def valid_composable_eq(c: ComposableEq):
    d, e = c
    return d.ssource.source.equiv(e.starget.target)

def compose(c: Composable) -> Mor:
    # TODO: Handle weaken here?
    require(valid_composable(c))
    return _compose(c)

def trans(p: Path):
    require(valid_path(p))
    return _trans(p)

def eq_unique(s: EqUniqueSource):
    require(valid_path(s))
    return _eq_unique(s)

def associativity(s: AssociativitySource):
    require(valid_associativity_source(s))
    return _associativity(s)

def compose_eq(c: ComposableEq):
    # TODO: Handle weaken here?
    require(valid_composable_eq(c))
    return _compose_eq(c)