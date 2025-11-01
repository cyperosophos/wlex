from ..static.cart import *
from . import require

_terminal_mor_unique = terminal_mor_unique
_pairing = pairing
_pairing_unique = pairing_unique

def valid_terminal_mor(mor: TerminalMor):
    target = mor.target
    return target.identical(target.terminal())

def valid_span(s: Span):
    p, q = s
    return p.source.identical(q.source)

def valid_product_mor(pm: ProductMor):
    mor, p, q, p_eq, q_eq = pm
    source_pt = p.target.product(q.target)
    _p = source_pt.proj('x')
    _q = source_pt.proj('y')
    return (
        mor.source.identical(p.source)
        and mor.target.identical(source_pt)
        and _p.compose(mor).same(p_eq.ssource)
        and p.same(p_eq.starget)
        and _q.compose(mor).same(q_eq.ssource)
        and q.same(q_eq.starget)
    )

def terminal_mor_unique(mor: TerminalMor):
    require(valid_terminal_mor(mor))
    return _terminal_mor_unique(mor)

def pairing(s: Span):
    require(valid_span(s))
    return _pairing(s)

def pairing_unique(pm: ProductMor):
    require(valid_product_mor(pm))
    return _pairing_unique(pm)
