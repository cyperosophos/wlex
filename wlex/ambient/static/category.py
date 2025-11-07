"""Static model of `category` morphisms

Here static means that there is here only the minimal type checking supported
through type annotations.
"""
from ..cells import Obj, Mor, Eq

Path = tuple[Eq, Eq]
Composable = tuple[Mor, Mor]
ComposableEq = tuple[Eq, Eq]
EqUniqueSource = tuple[Eq, Eq]
AssociativitySource = tuple[Mor, Mor, Mor]

# We annotate return types here to make type annotations as explicit as
# signatures in the wlex files.

def source(mor: Mor) -> Obj:
    """Static model of morphism `category.source`"""
    return mor.source

def target(mor: Mor) -> Obj:
    """Static model of morphism `category.target`"""
    return mor.target

def compose(c: Composable) -> Mor:
    """Static model of morphism `category.compose`"""
    f, g = c
    return f.compose(g)

def identity(obj: Obj) -> Mor:
    """Static model of morphism `category.identity`"""
    return obj.identity()

def ssource(eq: Eq) -> Mor:
    """Static model of morphism `category.S.source`"""
    return eq.ssource

def starget(eq: Eq) -> Mor:
    """Static model of morphism `category.S.target`"""
    return eq.starget

def ref(mor: Mor) -> Eq:
    """Static model of morphism `category.S.S.P.ref`"""
    return mor.ref()

def trans(p: Path) -> Eq:
    """Static model of morphism `category.S.S.P.trans`"""
    f, g = p
    return f.trans(g)

def left_identity_law(mor: Mor) -> Eq:
    """Static model of morphism `category.left_identity_law`"""
    return mor.ref()

def right_identity_law(mor: Mor) -> Eq:
    """Static model of morphism `category.right_identity_law`"""
    return mor.ref()

def associativity(s: AssociativitySource) -> Eq:
    """Static model of morphism `category.associativity`"""
    f, g, h = s
    return f.compose(g).compose(h).ref()

def eq_signature(e: Eq):
    """Static model of morphism `category.S.eq`"""
    return ssource(e), starget(e)

def eq_unique(s: EqUniqueSource) -> Eq:
    """Static model of morphism `category.S.unique`"""
    d, _ = s
    return d

def sym(eq: Eq) -> Eq:
    """Static model of morphism `category.S.S.sym`"""
    return eq.sym()

def compose_eq(c: ComposableEq) -> Eq:
    """Static model of morphism `category.compose_eq`"""
    d, e = c
    return d.compose_eq(e)
