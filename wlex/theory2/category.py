# pylint: disable=C0103, R0902, R0914, C0115, C0114
from dataclasses import dataclass
from typing import Any, Self

from wlex.ambient.category import (
    Obj as MetaObj, Mor as MetaMor, Eq as MetaEq, Theory, TheoryStub, composer,
    MorStub, EqStub,
)
from wlex.ambient.category import one as _, composer, transitivity
from wlex.ambient.cart import pairer0, producer
from wlex.ambient.lex import Context, requirer, prover
from .quiver import Quiver, QuiverStub, BasicQuiverStub
from .posetoid import Posetoid, PosetoidStub, Congruence, CongruenceStub, SetoidStub

@dataclass
class CategoryStub:
    Q: QuiverStub | None = None
    P: PosetoidStub | None = None
    S: CongruenceStub | None = None

    left_identity_law: MorStub | None = None
    right_identity_law: MorStub | None = None
    associativity: MorStub | None = None
    left_identity_law_hat: EqStub | None = None
    right_identity_law_hat: EqStub | None = None
    associativity_hat: EqStub | None = None

    compose_eq: MorStub | None = None
    compose_eq_hat: EqStub | None = None

    def with_base(self, base: Self):
        return type(self)(
            Q=_(self.Q, base.Q),
            P=_(self.P, base.P),
            S=_(self.S, base.S),
            left_identity_law=_(self.left_identity_law, base.left_identity_law),
            right_identity_law=_(self.right_identity_law, base.right_identity_law),
            associativity=_(self.associativity, base.associativity),
            left_identity_law_hat=_(self.left_identity_law_hat, base.left_identity_law_hat),
            right_identity_law_hat=_(self.right_identity_law_hat, base.right_identity_law_hat),
            associativity_hat=_(self.associativity_hat, base.associativity_hat),
            compose_eq=_(self.compose_eq, base.compose_eq),
            compose_eq_hat=_(self.compose_eq_hat, base.compose_eq_hat),
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
    left_identity_law_hat: MetaEq
    right_identity_law_hat: MetaEq
    associativity_hat: MetaEq

    ComposableEq: MetaObj

    compose_eq: MetaMor
    compose_eq_hat: MetaEq

    @classmethod
    def from_prim(cls, ctx: Context, prim: CategoryStub) -> Self:
        c = composer(ctx)
        t = transitivity(ctx)
        p = pairer0(ctx)
        product = producer(ctx)
        require = requirer(ctx)
        prove = prover(ctx)
        proj = ctx.proj
        i = ctx.id

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
        Obj = P.El # TODO: Set name by using ctx.obj, etc. Create copy?
        Mor = P.Rel
        Eq = S.Eq
        eq = S.eq
        source = P.source
        target = P.target
        Composable = P.Path
        identity = P.ref
        identity_hat = P.ref_hat
        compose = P.trans
        compose_hat = P.trans_hat

        # TODO: One should not distinguish subobjects based on the direction
        # of the requirement equalities. One way to accomplish is to include
        # the results of sym as elements in sets created for comparing the
        # subobjects. Besides, take a look again at the effect of naming on
        # comparison of subobjects and products. diff = 0 does not appear to
        # be symmetric (in contrast to identical). Notice use of sym in _fit_eq
        # for adapting equality to signature. Something like this would be
        # justifyied when providing proofs, so that they get adapted to the
        # requirements (which get composed with the morphism to create a signature).
        # The direction of equalities should not affect composition matching of
        # target and source. It may be possible to not point explicitly tp eq proofs,
        # but to automatically find them, since the search space is small.
        # This may be supported at a higher level. Not only is the search space
        # small, but all equalities may be registered with their signature as key
        # (accounting for sym can be done during search or during registration).
        # If an equality has been proven, then all that is needed to access it is
        # its signature. In fact in compositions where the target does not have the
        # requirements of the source can have a conversion (inclusion) automatically inferred.
        # Since there is not much accessing of equalities through names, it'd make
        # sense not to distinguish subobjects base on requirement naming.
        proof_lil = ... # This is just an Eq
        left_identity_law = ctx.mor(
            'left_identity_law', _(prim.left_identity_law), (
            c(p(('', c(
                compose,
                p(('', c(i, target)), ('', i)),
            )), ('', i)), Mor),
            eq,
        ))

        return super().from_prim(ctx, prim)
