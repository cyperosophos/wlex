from ..ambient import Obj as MObj, Mor as MMor
from .category import Category

class Cart:
    C: Category
    Obj: MObj
    Mor: MObj
    Eq: MObj
    eq: MMor
    source: MMor
    target: MMor
    compose: MMor
    terminal: MMor
    TerminalMor: MObj
    terminal_mor: MMor
    terminal_mor_unique: MMor

    Span: MObj

    product: MMor
    pt: MMor
    ProductMor: MObj

    pairing: MMor
    pairing_unique: MMor

    SpanEq: MObj
    pairing_eq: MMor
    
    def __init__(self, ambient):
        th = ambient.lex(self)
        c = th.compose
        t = th.trans
        p = th.pair
        th.sub('C', Category)
        C = self.C
        self.Obj = C.Obj
        self.Mor = C.Mor
        self.Eq = C.Eq
        self.eq = C.eq
        self.source = C.source
        self.target = C.target
        self.compose = C.compose
        th.obj('terminal')
        Mor = self.Mor
        target = self.target
        terminal = self.terminal
        self.TerminalMor = th.product(Mor).requiring(
            (target, terminal),
        )
        Obj = self.Obj
        source = self.source
        TerminalMor = self.TerminalMor
        th.mor(
            'terminal_mor',
            Obj,
            c(source, TerminalMor),
        )
        terminal_mor = self.terminal_mor
        eq = self.eq
        th.mor(
            'terminal_mor_unique',
            c(p(c(Mor, c(terminal_mor, source)), Mor), TerminalMor),
            eq,
        )

        Span = th.product(p=Mor, q=Mor).requiring(
            (source, ('p',), source, ('q',)),
        )

        p_, q = (th.proj(n) for n in 'pq')
        th.mor(
            'product',
            th.product(x=Obj, y=Obj),
            c(p(c(target, p_), c(target, q)), Span),
        )
        product = self.product
        self.pt = c(product, p(c(target, p_), c(target, q)), Span)
        pt = self.pt
        Eq = self.Eq
        compose = self.compose
        p_eq = th.proj('p_eq')
        q_eq = th.proj('q_eq')
        self.ProductMor = th.product(Mor, Span, p_eq=Eq, q_eq=Eq).requiring(
            (c(source, Mor), c(source, p_, Span)),
            (c(target, Mor), c(source, p_, pt)),
            (
                p(c(compose, p(c(p_, pt), Mor).where(th.req(1))), p_),
                c(eq, p_eq),
            ),
            (
                p(c(compose, p(c(q, pt), Mor).where(
                    # !1 & Span!0
                    t(th.req(1), th.req(Span, 0)),
                )), q),
                c(eq, q_eq),
            ),
        )

        ProductMor = self.ProductMor
        th.mor(
            'pairing',
            Span,
            c(Span, ProductMor),
        )
        pairing = self.pairing
        th.mor(
            'pairing_unique',
            c(p(c(Mor, pairing), Mor), ProductMor),
            eq, 
        )

        # !0 is short for $0 @ !<prod>
        x, y = (th.proj(n) for n in 'xy')
        self.SpanEq = self.product(
            x=Span, y=Span,
            p_eq=Eq, q_eq=Eq,
        ).requiring(
            (c(source, p_, x), c(source, p_, y)),
            (c(target, p_, x), c(target, p_, y)),
            (c(target, q, x), c(target, q, y)), 
            (p(c(p_, x), c(p_, y)), c(eq, p_eq)),
            (p(c(q, x), c(q, y)), c(eq, q_eq)),
        )

        pairing_unique = self.pairing_unique
        SpanEq = self.SpanEq
        pmy = p(
            Mor, y,
            c(C.S.S.P.trans, p(
                c(p_eq, SpanEq),
                c(p_eq, ProductMor),
            ).where(
                # ($0 @ SpanEq!3)
                # & ($p @ ^pairing @ $x)
                # & ($1 @ ProductMor!2 @ pairing @ $x)
                t(
                    c(th.proj(0), th.req(SpanEq, 3)),
                    c(p_, pairing.hat, x),
                    c(th.proj(1), th.req(ProductMor, 2), pairing, x),
                ),
            )),
            c(C.S.S.P.trans, p(
                c(q_eq, SpanEq),
                c(q_eq, ProductMor),
            ).where(
                t(
                    c(th.proj(0), th.req(SpanEq, 4)),
                    c(q, pairing.hat, x),
                    c(th.proj(1), th.req(ProductMor, 3), pairing, x),
                ),
            )),
        ).where(
            # Notice that the requirements take the whole composition in the source and target
            # (unless skipped as in the case of $y @ SpanEq, etc.)
            # Notice that equality pairing does not support `where` since the source belonging to
            # the equalizer makes the target also belong.
            # SpanEq!0 & (source @ $p @ ^pairing @ $x) & (ProductMor!0 @ pairing @ $x)
            t(th.req(SpanEq, 0), c(source, p, pairing.hat, x), c(th.req(ProductMor, 0), pairing, x)),
            # (source @ $p @ product @ (SpanEq!1, SpanEq!2))
            # & (source @ $p @ product @ (target @ $p, target @ $q) @ ^pairing @ x)
            # & (ProductMor!1 @ pairing @ $x)
            t(
                c(source, p_, product, p(th.req(SpanEq, 1), th.req(SpanEq, 2))),
                c(source, p_, product, p(c(target, p_), c(target, q)), pairing.hat, x),
                c(th.req(ProductMor, 1), pairing, x),
            ),
            # S.source:
            # ($0 @ ^trans @ (p_eq @ SpanEq, p_eq @ ProductMor) @ pairing @ $x)
            # & ($0 @ ProductMor!2 @ pairing @ $x)
            # & (compose @ ($p @ product @ (target @ $p, target @ $q) @ ^pairing, Mor @ pairing) @ $x)
            # & (compose @ ($p @ product @ (SpanEq!1, SpanEq!2), Mor @ pairing @ $x))
            # S.target:
            # $1 @ ^trans @ pairing @ $x
            p(
                t(
                    c(th.proj(0), C.S.S.P.trans.hat, p(
                        c(p_eq, SpanEq),
                        c(p_eq, ProductMor),
                    ), pairing, x),
                    c(th.proj(0), th.req(ProductMor, 2), pairing, x),
                    c(
                        compose,
                        p(
                            c(p_, product, p(c(target, p_), c(target, q)), pairing.hat),
                            c(Mor, pairing),
                        ),
                        x,
                    ),
                    c(
                        compose,
                        p(
                            c(p_, product, p(th.req(SpanEq, 1), th.req(SpanEq, 2))),
                            c(Mor, pairing, x),
                        )
                    )
                ),
                c(th.proj(1), C.S.S.P.trans.hat, p(
                    c(p_eq, SpanEq),
                    c(p_eq, ProductMor),
                ), pairing, x),
            ),
            p(
                t(
                    c(th.proj(0), C.S.S.P.trans.hat, p(
                        c(q_eq, SpanEq),
                        c(q_eq, ProductMor),
                    ), pairing, x),
                    c(th.proj(0), th.req(ProductMor, 3), pairing, x),
                    c(
                        compose,
                        p(
                            c(q, product, p(c(target, p_), c(target, q)), pairing.hat),
                            c(Mor, pairing),
                        ),
                        x,
                    ),
                    c(
                        compose,
                        p(
                            c(q, product, p(th.req(SpanEq, 1), th.req(SpanEq, 2))),
                            c(Mor, pairing, x),
                        )
                    )
                ),
                c(th.proj(1), C.S.S.P.trans.hat, p(
                    c(q_eq, SpanEq),
                    c(q_eq, ProductMor),
                ), pairing, x),
            ),
        )
        pairing_eq = c(
            C.S.S.sym,
            pairing_unique,
            pmy,
            pairing,
            x,
        )
        th.mor(
            'pairing_eq',
            c(p(c(Mor, pairing, x), c(Mor, pairing, y)), SpanEq),
            eq,
            pairing_eq,
            # (($1 @ ^pairing_unique) & (^sym @ pairing_unique)) @ pmy @ pairing @ x
            c(
                t(
                    c(th.proj(1), pairing_unique.hat),
                    c(C.S.S.sym.hat, pairing_unique)
                ),
                pmy, pairing, x,
            ),
        )


