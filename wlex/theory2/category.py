# pylint: disable=C0103, R0902, R0914, C0115, C0114
from dataclasses import dataclass
from typing import Self

from wlex.ambient.category import (
    Obj as MetaObj, Mor as MetaMor, Eq as MetaEq, Theory, TheoryStub,
    MorStub, EqStub, one as _
)
from wlex.ambient.lex import LexContext
from .quiver import Quiver, QuiverStub, BasicQuiverStub
from .posetoid import Posetoid, PosetoidStub, Congruence, CongruenceStub, SetoidStub

@dataclass
class CategoryStub(TheoryStub):
    Q: QuiverStub | None = None
    P: PosetoidStub | None = None
    S: CongruenceStub | None = None

    left_identity_law: MorStub | None = None
    right_identity_law: MorStub | None = None
    associativity: MorStub | None = None
    #left_identity_law_hat: EqStub | None = None
    #right_identity_law_hat: EqStub | None = None
    #associativity_hat: EqStub | None = None

    compose_eq: MorStub | None = None
    #compose_eq_hat: EqStub | None = None

    eqs: tuple[EqStub | None, EqStub | None, EqStub | None, EqStub | None] = (None, None, None, None)

    def with_base(self, base: Self):
        eqs = tuple(_(s, b) for s, b in zip(self.eqs, base.eqs))
        assert len(eqs) == 4
        return type(self)(
            Q=_(self.Q, base.Q),
            P=_(self.P, base.P),
            S=_(self.S, base.S),
            left_identity_law=_(self.left_identity_law, base.left_identity_law),
            right_identity_law=_(self.right_identity_law, base.right_identity_law),
            associativity=_(self.associativity, base.associativity),
            #left_identity_law_hat=_(self.left_identity_law_hat, base.left_identity_law_hat),
            #right_identity_law_hat=_(self.right_identity_law_hat, base.right_identity_law_hat),
            #associativity_hat=_(self.associativity_hat, base.associativity_hat),
            compose_eq=_(self.compose_eq, base.compose_eq),
            #compose_eq_hat=_(self.compose_eq_hat, base.compose_eq_hat),
            eqs=eqs,
        )

@dataclass
class Category(Theory):
    Q: Quiver
    P: Posetoid
    S: Congruence
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
    #left_identity_law_hat: MetaEq
    #right_identity_law_hat: MetaEq
    #associativity_hat: MetaEq

    ComposableEq: MetaObj

    compose_eq: MetaMor
    #compose_eq_hat: MetaEq

    eqs: tuple[MetaEq, MetaEq, MetaEq, MetaEq]

    @classmethod
    def from_prim(cls, ctx: LexContext, prim: CategoryStub) -> Self:
        c = ctx.c
        t = ctx.t
        p = ctx.pair
        prod = ctx.prod
        req = ctx.req
        proj = ctx.proj
        i = ctx.id
        l = ctx.l

        Q = ctx.sub('Q', Quiver, _(prim.Q))
        P = ctx.sub('P', Posetoid, _(prim.P), PosetoidStub(
            Q=BasicQuiverStub.from_theory(Q.Q0),
        ))
        S = ctx.sub('S', Congruence, _(prim.S), CongruenceStub(
            S=SetoidStub(
                P=PosetoidStub(
                    Q=BasicQuiverStub.from_theory(Q.Q1)
                )
            )
        ))
        Obj = P.El
        Mor = P.Rel
        Eq = S.Eq
        eq = S.eq
        source = P.source
        target = P.target
        Composable = P.Path
        P_ref_hat, P_trans_hat = P.eqs
        identity = P.ref
        identity_hat = P_ref_hat
        compose = P.trans
        compose_hat = P_trans_hat

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

        return cls(
            Q=Q,
            P=P,
            S=S,
            Obj=Obj,
            Mor=Mor,
            Eq=Eq,
            eq=eq,
            source=source,
            target=target,
            Composable=Composable,
            identity=identity,
            compose=compose,
            left_identity_law=left_identity_law,
            right_identity_law=right_identity_law,
            associativity=associativity,
            ComposableEq=ComposableEq,
            compose_eq=compose_eq,
            eqs=(...),
        )
