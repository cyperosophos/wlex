from ..ambient import Obj as MObj, Mor as MMor
from .cart import Cart

class Lex:
    C: Cart
    Obj: MObj
    Mor: MObj
    Eq: MObj
    eq: MMor
    source: MMor
    target: MMor
    compose: MMor

    Parallel: MObj
    Fork: MObj

    equalizer: MMor

    meqp: MMor
    EqualizerMor: MObj

    equalizer_pairing: MMor
    equalizer_pairing_unique: MMor

    def __init__(self, theory):
        th = theory.lex(self)
        c = th.compose
        t = th.trans
        p = th.pair
        th.sub('C', Cart)
        C = self.C
        self.Obj = C.Obj
        self.Mor = C.Mor
        self.Eq = C.Eq
        self.eq = C.eq
        self.source = C.source
        self.target = C.target
        self.compose = C.compose

        Mor = self.Mor
        source = self.source
        target = self.target
        i, j = (th.proj(n) for n in 'ij')
        self.Parallel = th.product(i=Mor, j=Mor).requiring(
            (
                c(p(source, target), i),
                c(p(source, target), j),
            ),
        )
        Parallel = self.Parallel
        Eq = self.Eq
        eq = self.eq
        compose = self.compose
        self.Fork = th.product(Mor, Parallel, Eq).requiring(
            (c(source, i), c(target, Mor)),
            (p(
                c(compose, p(i, Mor).where(th.req(0))),
                c(compose, p(j, Mor).where(t(
                    c(th.proj(0), th.req(Parallel, 0)),
                    th.req(0),
                ))),
            ), eq),
        )

        Fork = self.Fork
        th.mor(
            'equalizer',
            Parallel,
            c(Parallel, Fork),
        )

        equalizer = self.equalizer
        self.meqp = c(Mor, equalizer, Parallel)
        meqp = self.meqp
        self.EqualizerMor = th.product(Mor, Fork, Eq).requiring(
            (c(source, Mor), c(source, Mor, Fork)),
            (c(target, Mor), c(source, meqp)),
            (p(c(
                compose,
                p(meqp, Mor).where(th.req(1)),
            ), c(Mor, Fork)), eq)
        )

        EqualizerMor = self.EqualizerMor
        th.mor(
            'equalizer_pairing',
            Fork,
            c(Fork, EqualizerMor),
        )
        equalizer_pairing = self.equalizer_pairing
        th.mor(
            'equalizer_pairing_unique',
            c(p(c(Mor, equalizer_pairing), Mor), EqualizerMor),
            eq,
        )
