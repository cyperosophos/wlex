#from collections.abc import Sequence

from ..cells import Obj, Mor, Eq

TerminalMor = Mor
ObjObj = tuple[Obj, Obj]
Span = tuple[Mor, Mor]
ProductMor = tuple[Mor, Mor, Mor, Eq, Eq]
#SpanEq = tuple[Span, Span, Eq, Eq]

def terminal_mor(obj: Obj):
    return obj.terminal_mor()

def terminal_mor_unique(mor: TerminalMor):
    return mor.terminal_mor_unique()

def product(xy: ObjObj):
    x, y = xy
    return x.product(y)

def pairing(s: Span):
    p, q = s
    return p.pairing(q)

def pairing_unique(pm: ProductMor):
    mor, p, q, _, _ = pm
    return mor.pairing_unique(p, q)