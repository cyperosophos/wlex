from ..cells import Obj, Mor, Eq

Path = tuple[Eq, Eq]
Composable = tuple[Mor, Mor]
ComposableEq = tuple[Eq, Eq]
EqUniqueSource = tuple[Eq, Eq]
AssociativitySource = tuple[Mor, Mor, Mor]

# We use explicit return types here in order to mimic category.lex
# as much as possible.

def source(mor: Mor) -> Obj:
    return mor.source

def target(mor: Mor) -> Obj:
    return mor.target

def compose(c: Composable) -> Mor:
    # Theoretical compose
    f, g = c
    return f.compose(g)
    
def identity(obj: Obj) -> Mor:
    return obj.identity()

def ssource(eq: Eq) -> Mor:
    return eq.ssource

def starget(eq: Eq) -> Mor:
    return eq.starget

def ref(mor: Mor) -> Eq:
    return mor.ref()

def trans(p: Path) -> Eq:
    f, g = p
    return f.trans(g)

def eq_unique(s: EqUniqueSource) -> Eq:
    d, _ = s
    return d

def sym(eq: Eq) -> Eq:
    return eq.sym()

def associativity(s: AssociativitySource) -> Eq:
    f, g, h = s
    # Type checking s and return value is enough.
    return f.compose(g).compose(h).ref()

def compose_eq(c: ComposableEq) -> Eq:
    d, e = c
    return d.compose_eq(e)

# TODO: left_identity
# TODO: right_identity
