# pylint: disable=C0103, R0902, C0115, C0114
from dataclasses import dataclass
from typing import Self

from wlex.ambient.cells import (
    Obj as MetaObj, Mor as MetaMor, MorStub, EqStub,
)
from wlex.ambient.category import (
    Context, Theory, Once as _o, OnceStub as _s, OnceUpdate as _u,
    of_type as _ot,
)
from wlex.ambient.lex import LexContext

from .quiver import (
    QuiverStub, QuiverTheory, Quiver,
)
from .posetoid import (
    PosetoidStub, PosetoidTheory, Posetoid,
    CongruenceStub, CongruenceTheory, Congruence,
)

@dataclass(frozen=True)
class CategoryStub:
    Q: _s[QuiverStub]
    P: _s[PosetoidStub]
    S: _s[CongruenceStub]

    left_identity_law: _o[MorStub]
    right_identity_law: _o[MorStub]
    associativity: _o[MorStub]
    left_identity_law_hat: _o[EqStub]
    right_identity_law_hat: _o[EqStub]
    associativity_hat: _o[EqStub]

    compose_eq: _o[MorStub]
    compose_eq_hat: _o[EqStub]

@dataclass(frozen=True)
class CategoryTheory(Theory):
    Q: QuiverTheory
    P: PosetoidTheory
    S: CongruenceTheory
    Obj: MetaObj
    Mor: MetaObj
    Eq: MetaObj
    eq: MetaMor
    source: MetaMor
    target: MetaMor
    Composable: MetaObj
    identity: MetaMor
    compose: MetaMor

    left_identity_law: MetaMor
    right_identity_law: MetaMor
    associativity: MetaMor

    ComposableEq: MetaObj
    compose_eq: MetaMor

    @classmethod
    def from_ctx(cls, ctx: Context[Self]):
        return cls(
            Q=_ot(ctx.sub_refs['Q'], QuiverTheory),
            P=_ot(ctx.sub_refs['P'], PosetoidTheory),
            S=_ot(ctx.sub_refs['S'], CongruenceTheory),
            Obj=ctx.obj_refs['Obj'],
            Mor=ctx.obj_refs['Mor'],
            Eq=ctx.obj_refs['Eq'],
            eq=ctx.mor_refs['eq'],
            source=ctx.mor_refs['source'],
            target=ctx.mor_refs['target'],
            Composable=ctx.obj_refs['Composable'],
            identity=ctx.mor_refs['identity'],
            compose=ctx.mor_refs['compose'],
            left_identity_law=ctx.mor_refs['left_identity_law'],
            right_identity_law=ctx.mor_refs['right_identity_law'],
            associativity=ctx.mor_refs['associativity'],
            ComposableEq=ctx.obj_refs['ComposableEq'],
            compose_eq=ctx.mor_refs['compose_eq'],
        )

def Category(stub: _u[CategoryStub]):
    ctx = LexContext(CategoryTheory)
    prim = _o.prim(stub)
    c = ctx.c
    t = ctx.t
    p = ctx.pair
    prod = ctx.prod
    req = ctx.req
    proj = ctx.proj
    i = ctx.id
    l = ctx.l

    Q = ctx.sub('Q', Quiver(prim.Q))

    def P_update(stub: PosetoidStub):
        Q.Q0.stub_update(stub.Q.stub)

    P = ctx.sub('P', Posetoid((prim.P, P_update)))

    def S_update(stub: CongruenceStub):
        Q.Q1.stub_update(stub.S.stub.P.stub.Q.stub)

    S = ctx.sub('S', Congruence((prim.S, S_update)))

    _ = ctx.define('Obj', P.El)
    Mor = ctx.define('Mor', P.Rel)
    Eq = ctx.define('Eq', S.Eq)
    eq = ctx.define('eq', S.eq)
    source = ctx.define('source', P.source)
    target = ctx.define('target', P.target)
    Composable = ctx.define('Composable', P.Path)
    identity = ctx.define('identity', P.ref)
    compose = ctx.define('compose', P.trans)

    # TODO: There is overlap of eq and t (and prove).
    # There is overlap of el and define, and of mor and define.
    # TODO: When registering equalities of pairings, register instead
    # each component separately. Same applies for EqualizerMor.
    # The idea is that in one case one composes with projs and in the other with incls.

    ctx.eq(c(t(c(source, identity), i), target))
    _, _left_identity_law_hat = ctx.mor('left_identity_law', prim.left_identity_law, (
        Mor, Eq,
        p(c(
            compose,
            p(c(identity, target), i),
        ), i),
        eq,
    ))
    _left_identity_law_hat(prim.left_identity_law_hat)

    ctx.eq(c(t(c(target, identity), i), source))
    _, _right_identity_law_hat = ctx.mor('right_identity_law', prim.right_identity_law, (
        Mor, Eq,
        p(c(
            compose,
            p(i, c(identity, source)),
        ), i),
        eq,
    ))
    _right_identity_law_hat(prim.right_identity_law_hat)

    Comp3 = prod(('', Composable), ('', l(Composable, ('g', 'h'))))
    f, g, h = (proj(n) for n in 'fgh')
    ctx.eq(t(
        c(
            t(c(target, compose), c(target, f)),
            p(('f', g), ('g', h)),
        ),
        f,
    ))
    ctx.eq(t(
        h,
        t(c(source, compose), c(target, g)),
    ))
    _, _associativity_hat = ctx.mor('associativity', prim.associativity, (
        Comp3, Eq,
        p(
            c(compose, p(f, c(compose, p(g, h)))),
            c(compose, p(c(compose, p(f, g)), h)),
        ),
        eq,
    ))
    _associativity_hat(prim.associativity_hat)

    d, e = (proj(n) for n in 'de')
    ComposableEq = req(
        prod(('d', Eq), ('e', Eq)), (
        c(source, S.source, d),
        c(target, S.target, e),
    ))
    ctx.eq(t(
        c(t(
            c(target, S.source),
            c(target, S.target),
        ), e),
        c(target, S.target, e),
        c(source, S.source, d),
    ))
    ctx.eq(t(
        c(target, S.target, e),
        c(source, S.source, d),
        c(t(
            c(source, S.source),
            c(source, S.target),
        ), d),
    ))
    _, _compose_eq_hat = ctx.mor('compose_eq', prim.compose_eq, (
        ComposableEq, Eq,
        p(
            c(compose, p(c(S.source, d), c(S.source, e))),
            c(compose, p(c(S.target, d), c(S.target, e))),
        ),
        eq,
    ))
    _compose_eq_hat(prim.compose_eq_hat)

    return ctx