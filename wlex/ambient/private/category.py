"""Private model of `category` morphisms

Here private means that there is only the minimal type checking supported
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

def source_globular_cond(eq: Eq):
    """Models equality `category.Q.source_globular_cond` (public)"""
    return eq.ssource.source.identical(eq.starget.source)

def target_globular_cond(eq: Eq):
    """Models equality `category.Q.target_globular_cond` (public)"""
    return eq.ssource.target.identical(eq.starget.target)

def is_eq(eq: Eq):
    """Models requirements of equalities with source `Eq`"""
    return source_globular_cond(eq) and target_globular_cond(eq)

def is_composable(c: Composable):
    """Models requirement of `category.Composable`"""
    f, g = c
    return source(f).identical(target(g))

def is_path(p: Path):
    """Models requirement of `category.S.S.P.Path`"""
    f, g = p
    return (
        is_eq(f) and is_eq(g)
        and ssource(f).same(starget(g))
    )

def is_eq_unique_source(s: EqUniqueSource):
    """Models requirement of source of `category.S.unique`"""
    d, e = s
    return (
        is_eq(d) and is_eq(e)
        and ssource(d).same(ssource(e))
        and starget(d).same(starget(e))
    )

def is_associativity_source(s: AssociativitySource):
    """Models requirement of source of `category.associativity`"""
    f, g, h = s
    return is_composable((f, g)) and is_composable((g, h))

def is_composable_eq(c: ComposableEq):
    """Models requirement of `category.ComposableEq`"""
    d, e = c
    return (
        is_eq(d) and is_eq(e)
        and source(ssource(d)).identical(target(starget(e)))
    )

def source(mor: Mor) -> Obj:
    """Models morphism `category.source`"""
    return mor.source

def target(mor: Mor) -> Obj:
    """Models morphism `category.target`"""
    return mor.target

def compose(c: Composable) -> Mor:
    """Model of morphism `category.compose`"""
    f, g = c
    return f.compose(g)

def compose_hat(c: Composable):
    """Models hat equality of `category.compose`"""
    h = compose(c)
    f, g = c
    return source(g).identical(source(h)) and target(f).identical(target(h))

def identity(obj: Obj) -> Mor:
    """Models of morphism `category.identity`"""
    return obj.identity()

def identity_hat(obj: Obj):
    """Models hat equality of `category.identity`"""
    id_ = identity(obj)
    return obj.identical(source(id_)) and obj.identical(target(id_))

def ssource(eq: Eq) -> Mor:
    """Model of morphism `category.S.source`"""
    return eq.ssource

def starget(eq: Eq) -> Mor:
    """Model of morphism `category.S.target`"""
    return eq.starget

def ref(mor: Mor) -> Eq:
    """Models morphism `category.S.S.P.ref`"""
    return mor.ref()

def ref_hat(mor: Mor):
    """Models hat equality of `category.S.S.P.ref`"""
    r = ref(mor)
    return mor.same(ssource(r)) and mor.same(starget(r))

def trans(p: Path) -> Eq:
    """Model of morphism `category.S.S.P.trans`"""
    f, g = p
    return f.trans(g)

def trans_hat(p: Path):
    """Models hat equality of `category.S.S.P.trans`"""
    h = trans(p)
    f, g = p
    return ssource(g).same(ssource(h)) and starget(f).same(starget(h))

def left_identity_law(mor: Mor) -> Eq:
    """Model of morphism `category.left_identity_law`"""
    return mor.ref()

def left_identity_law_hat(mor: Mor):
    """Models hat equality of `category.left_identity_law`"""
    s, t = eq_signature(left_identity_law(mor))
    return (
        compose((identity(target(mor)), mor)).same(s)
        and mor.same(t)
    )

def right_identity_law(mor: Mor) -> Eq:
    """Model of morphism `category.right_identity_law`"""
    return mor.ref()

def right_identity_law_hat(mor: Mor):
    """Models hat equality of `category.right_identity_law`"""
    s, t = eq_signature(left_identity_law(mor))
    return (
        compose((mor, identity(source(mor)))).same(s)
        and mor.same(t)
    )

def associativity(s: AssociativitySource) -> Eq:
    """Model of morphism `category.associativity`"""
    f, g, h = s
    return f.compose(g).compose(h).ref()

def associativity_hat(src: AssociativitySource):
    """Models hat equality of `category.associativity`"""
    s, t = eq_signature(associativity(src))
    f, g, h = src
    return (
        compose((f, compose((g, h)))).same(s)
        and compose((compose((f, g)), h)).same(t)
    )

def eq_signature(eq: Eq):
    """Model of morphism `category.S.eq`"""
    return ssource(eq), starget(eq)

def eq_unique(s: EqUniqueSource) -> Eq:
    """Model of morphism `category.S.unique`"""
    d, _ = s
    return d

def eq_unique_hat(s: EqUniqueSource):
    """Models hat equality for `category.S.unique`"""
    r = eq_unique(s)
    d, e = s
    return d.parallel(r) and e.parallel(r)

def sym(eq: Eq) -> Eq:
    """Model of morphism `category.S.S.sym`"""
    return eq.sym()

def sym_hat(eq: Eq):
    """Models hat equality for `category.S.S.sym`"""
    r = sym(eq)
    return ssource(eq).same(starget(r)) and starget(eq).same(ssource(r))

def compose_eq(c: ComposableEq) -> Eq:
    """Model of morphism `category.compose_eq`"""
    d, e = c
    return d.compose_eq(e)

def compose_eq_hat(c: ComposableEq):
    """Models hat equality for `category.compose_eq`"""
    s, t = eq_signature(compose_eq(c))
    d, e = c
    return (
        compose((ssource(d), ssource(e))).same(s)
        and compose((starget(d), starget(e))).same(t)
    )
