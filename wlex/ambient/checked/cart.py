from ..static.cart import *
from . import require

_terminal_mor_unique = terminal_mor_unique
_pairing = pairing
_pairing_unique = pairing_unique

def valid_terminal_mor(mor: TerminalMor):
    target = mor.target
    return target.equiv(target.terminal())

def valid_span(s: Span):
    p, q = s
    return p.source.equiv(q.source)

def valid_product_mor(pm: ProductMor):
    mor, p, q, p_eq, q_eq = pm
    pt = p.target.product(q.target)
    pt_p, pt_q = pt
    return (
        mor.source.equiv(p.source)
        and mor.target.equiv(pt_p.source)
        and pt_p.compose(mor).eql(p_eq.ssource)
        and p.eql(p_eq.starget)
        and pt_q.compose(mor).eql(q_eq.ssource)
        and q.eql(q_eq.starget)
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
