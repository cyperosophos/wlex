from .cell import Obj, Mor, Eq, Limit
from .quiver import BasicQuiver

class Posetoid:
    Q: BasicQuiver
    El: Obj
    Rel: Obj
    source: Mor
    target: Mor
    Path: Limit # Limit can be anonymous
    ref: Mor # May include triangle
    trans: Mor

    def __init__(self, theory):
        th = theory.lex(self)
        c = th.compose
        p = th.pair
        th.sub('Q', BasicQuiver)
        Q = self.Q
        self.El = Q.Node
        self.Rel = Q.Edge
        self.source = Q.source
        self.target = Q.target
        El = self.El
        Rel = self.Rel
        source = self.source
        target = self.target

        self.Path = th.product(f=Rel, g=Rel).requiring(
            (source, ('f',), target, ('g',)),
        )
        Path = self.Path

        th.mor(
            'ref',
            c(p(th.id, th.id), El),
            p(source, target),
        )
        f, g = (th.proj(n) for n in 'fg')
        th.mor(
            'trans',
            c(p(
                c(source, g),
                c(target, f),
            ), Path),
            p(source, target),
        )

class Setoid:
    P: Posetoid
    Eq: Obj
    source: Mor
    target: Mor
    sym: Mor

    def __init__(self, theory):
        th = theory.lex(self)
        p = th.pair
        th.sub('P', Posetoid)
        P = self.P
        self.Eq = P.Rel
        self.source = P.source
        self.target = P.target
        source = self.source
        target = self.target

        th.mor(
            'sym',
            p(source, target),
            p(target, source),
        )

class Congruence:
    S: Setoid
    Eq: Obj
    source: Mor
    target: Mor
    eq: Mor
    unique: Mor

    def __init__(self, theory):
        th = theory.lex(self)
        c = th.compose
        p = th.pair
        th.sub('S', Setoid)
        S = self.S
        self.Eq = S.Eq
        self.source = S.source
        self.target = S.target
        Eq = self.Eq
        source = self.source
        target = self.target
        self.eq = p(source, target)
        eq = self.eq
        th.mor(
            'unique',
            th.product(d=Eq, e=Eq).requiring(
                (eq, ('d',), eq, ('e',)),
            ),
            c(p(th.id, th.id), Eq),
        )

