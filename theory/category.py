from .cell import Obj as MObj, Mor as MMor, Eq as MEq, Limit
from .quiver import Quiver
from .posetoid import Posetoid, Congruence

class Category:
    Q: Quiver
    P: Posetoid
    S: Congruence
    Obj: MObj
    Mor: MObj
    Eq: MObj
    eq: MMor
    source: MMor
    target: MMor
    Composable: Limit
    identity: MMor
    compose: MMor

    left_identity_law: MMor
    right_identity_law: MMor
    associativity: MMor

    ComposableEq: Limit

    compose_eq: MMor

    def __init__(self, theory):
        th = theory.lex(self)
        c = th.compose
        t = th.trans
        p = th.pair
        th.sub('Q', Quiver)
        Q = self.Q
        th.sub('P', Posetoid, Q=Q.Q0)
        th.sub('S', Congruence, **{'S.P.Q': Q.Q1})
        P = self.P
        S = self.S
        self.Obj = P.El
        self.Mor = P.Rel
        self.Eq = S.Eq
        self.eq = S.eq
        self.source = P.source
        self.target = P.target
        self.Composable = P.Path
        self.identity = P.ref
        self.compose = P.trans
        Mor = self.Mor
        Eq = self.Eq
        eq = self.eq
        source = self.source
        target = self.target
        Composable = self.Composable
        identity = self.identity
        compose = self.compose

        # TODO: Too many implicit steps? (e.g. assoc, id laws, sym, p_eq)
        # $0 @ ^identity @ target
        proof_lil = c(th.proj(0), identity.hat, target)
        th.mor(
            'left_identity_law',
            c(p(c(
                compose,
                p(c(identity, target), th.id).where(proof_lil),
            ), th.id), Mor),
            eq,
        )
        # $1 @ ^identity @ source
        proof_ril = c(th.proj(1), identity.hat, source)
        th.mor(
            'right_identity_law',
            c(p(c(
                compose,
                p(th.id, c(identity, source)).where(proof_ril),
            ), th.id), Mor),
            eq,
        )
        f, g, h = (th.proj(n) for n in 'fgh')
        # $1
        # ($1 @ ^compose @ (g, h)) & !0
        # $0
        # !1 & ($0 @ ^compose) # Automatically uses (f, g).
        proof_assocl = t(
            c(
                c(th.proj(1), compose.hat),
                p(g, h).where(th.req(1)),
            ),
            th.req(0),
        )
        proof_assocr = t(
            th.req(1),
            c(th.proj(0), compose.hat),
        )
        th.mor(
            'associativity',
            c(p(
                c(compose, p(f, c(compose, p(g, h).where(
                    th.req(1),
                ))).where(proof_assocl)),
                c(compose, p(c(compose, p(f, g).where(
                    th.req(0),
                )), h).where(proof_assocr)),
            ), th.product(
                Composable,
                (('g', 'h'), Composable),
            )),
            eq,
        )

        self.ComposableEq = th.product(d=Eq, e=Eq).requiring(
            (
                c(source, S.source), ('d',),
                c(target, S.target), ('e',),
            ),
        )
        ComposableEq = self.ComposableEq

        d, e = (th.proj(n) for n in 'de')
        # (Q.target_globular_cond @ $e) & !0
        proof_compsrc = t(c(Q.target_globular_cond, e), th.req(0))
        # !1 @ (Q.source_globular_cond @ $d)
        proof_comptgt = t(th.req(0), c(Q.source_globular_cond, d))
        th.mor(
            'compose_eq',
            c(p(
                c(compose, p(c(S.source, d), c(S.source, e)).where(proof_compsrc)),
                c(compose, p(c(S.target, d), c(S.target, e)).where(proof_comptgt)),
            ), ComposableEq),
            eq,
        )



