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

    Obj = ctx.define('Obj', P.El)
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

    ctx.eq(c(
        c(proj(0), prod(Obj, Obj)).ref(),
        identity_hat, target,
    ))
    left_identity_law = ctx.mor(
        'left_identity_law', _(prim.left_identity_law), (
        Mor, Eq,
        p(c(
            compose,
            p(c(identity, target), i),
        ), i),
        eq,
    ))

    ctx.eq(c(
        c(proj(1), prod(Obj, Obj)).ref(),
        identity_hat, source,
    ))
    right_identity_law = ctx.mor(
        'right_identity_law', _(prim.right_identity_law), (
        Mor, Eq,
        p(c(
            compose,
            p(i, c(identity, source)),
        ), i),
        eq,
    ))

    Comp3 = prod(('', Composable), ('', l(Composable, ('g', 'h'))))
    f, g, h = (c(proj(n), Comp3) for n in 'fgh')
    ctx.eq(t(
        c(
            c(proj(1), compose_hat),
            p(g, h),
        ),
        f,
    ))
    ctx.eq(t(
        h,
        c(proj(0), compose_hat),
    ))
    associativity = ctx.mor(
        'associativity', _(prim.associativity), (
        Comp3, Eq,
        p(
            c(compose, p(f, c(compose, p(g, h)))),
            c(compose, p(c(compose, p(f, g)), h)),
        ),
        eq,
    ))

    ComposableEq = req(
        prod(('d', Eq), ('e', Eq)),
        (c(source, S.source), proj('d')),
        (c(target, S.target), proj('e'))
    )
    d, e = (c(proj(n), ComposableEq) for n in 'de')
    ctx.eq(t(
        c(Q.target_globular_cond, e),
        th.req(0),
    ))