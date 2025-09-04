import unittest
from wlex.ambient import category, Obj, Mor, Eq

class SampleSubSubTheory:
    Y: Obj
    h: Mor

    def __init__(self, ambient):
        th: category.Category = ambient(self)
        th.obj('Y')
        Y = self.Y
        th.mor('h', Y, Y)

class SampleSubTheory:
    X: Obj
    Y: Obj
    Z: Obj
    k: Mor
    l: Mor
    p: Eq

    SS: SampleSubSubTheory

    def __init__(self, ambient):
        th: category.Category = ambient(self)
        th.obj('X')
        th.obj('Y')
        th.obj('Z')
        X = self.X
        Y = self.Y
        Z = self.Z
        th.mor('k', X, Z)
        th.mor('l', X, Z)
        k = self.k
        l = self.l
        th.mor('p', k, l)

        th.sub('SS', SampleSubSubTheory, Y=Y)

class SampleTheory:
    X: Obj
    Y: Obj
    Z: Obj

    f: Mor
    g: Mor
    h: Mor
    i: Mor
    k: Mor
    l: Mor

    p: Eq
    q: Eq
    r: Eq
    s: Eq
    t: Eq
    u: Eq

    m: category.HatMor
    n: category.HatMor

    S: SampleSubTheory

    def __init__(self, ambient):
        th: category.Category = ambient(self)
        c = th.compose
        t = th.trans
        th.obj('X')
        th.obj('Y')
        th.obj('Z')
        X = self.X
        Y = self.Y
        Z = self.Z

        th.mor('f', X, Y)
        th.mor('g', Y, X)
        f = self.f
        g = self.g
        th.mor('h', Y, Y, c(f, g))
        th.mor('i', Y, Z)
        i = self.i
        th.mor('k', X, Z, c(i, f))
        th.mor('l', X, Z)
        h = self.h
        k = self.k
        l = self.l

        th.eq('p', k, l)
        th.eq('q', c(f, g), h)
        th.eq('r', i, c(i, h))
        p = self.p
        th.eq('s', c(g, l), c(g, k), c(g, p))
        th.eq('t', c(f, g, h), c(h, h))
        th.eq('u', l, c(i, f), p)

        th.mor('m', k, i, f, k)
        m = self.m
        th.mor('n', k, i, m, m.hat)

        th.sub(
            'S', SampleSubTheory,
            X=X,
            Y=Y,
            Z=Z,
            k=k,
            l=l,
            p=p,
            **{'SS.h': h},
        )

class MutableTheory:
    th: category.Category

    def __init__(self, ambient):
        self.th = ambient(self)

    @classmethod
    def tip(cls):
        return cls(lambda t: category.Category(t))

class TestCategory(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.theory = SampleTheory(lambda t: category.Category(t))

    def test_sample_theory_obj(self):
        X = self.theory.X
        Y = self.theory.Y
        Z = self.theory.Z
        SX = self.theory.S.X
        SY = self.theory.S.Y
        SZ = self.theory.S.Z
        SSY = self.theory.S.SS.Y

        self.assertIsInstance(X, Obj)
        self.assertIsInstance(Y, Obj)
        self.assertIsInstance(Z, Obj)
        self.assertEqual(X.name, 'X')
        self.assertEqual(Y.name, 'Y')
        self.assertEqual(Z.name, 'Z')

        self.assertIs(X, SX)
        self.assertIs(Y, SY)
        self.assertIs(Y, SSY)
        self.assertIs(Z, SZ)

    def test_sample_theory_mor(self):
        f = self.theory.f
        g = self.theory.g
        h = self.theory.h
        i = self.theory.i
        k = self.theory.k
        l = self.theory.l
        Sk = self.theory.S.k
        Sl = self.theory.S.l
        SSh = self.theory.S.SS.h

        X = self.theory.X
        Y = self.theory.Y
        Z = self.theory.Z

        self.assertIsInstance(f, Mor)
        self.assertIsInstance(g, Mor)
        self.assertIsInstance(h, Mor)
        self.assertIsInstance(i, Mor)
        self.assertIsInstance(k, Mor)
        self.assertIsInstance(l, Mor)
        self.assertEqual(f.name, 'f')
        self.assertEqual(g.name, 'g')
        self.assertEqual(h.name, 'h')
        self.assertEqual(i.name, 'i')
        self.assertEqual(k.name, 'k')
        self.assertEqual(l.name, 'l')
        self.assertEqual(k, Sk)
        self.assertEqual(l, Sl)
        self.assertEqual(Sk.name, 'S.k')
        self.assertEqual(Sl.name, 'S.l')
        self.assertEqual(h, SSh)
        self.assertEqual(SSh.name, 'S.SS.h')

        self.assertIs(f.source, X)
        self.assertIs(f.target, Y)
        self.assertIs(g.source, Y)
        self.assertIs(g.target, X)
        self.assertIs(h.source, Y)
        self.assertIs(h.target, Y)
        self.assertIs(i.source, Y)
        self.assertIs(i.target, Z)
        self.assertIs(k.source, X)
        self.assertIs(k.target, Z)
        self.assertIs(l.source, X)
        self.assertIs(l.target, Z)

        self.assertEqual(h, category.Comp(f, g))
        self.assertEqual(k, category.Comp(i, f))

    def test_sample_theory_eq(self):
        p = self.theory.p
        q = self.theory.q
        r = self.theory.r
        s = self.theory.s
        t = self.theory.t
        u = self.theory.u
        Sp = self.theory.S.p

        g = self.theory.g

        self.assertIsInstance(p, Eq)
        self.assertIsInstance(q, Eq)
        self.assertIsInstance(r, Eq)
        self.assertIsInstance(s, Eq)
        self.assertIsInstance(t, Eq)
        self.assertIsInstance(u, Eq)
        self.assertEqual(p.name, 'p')
        self.assertEqual(q.name, 'q')
        self.assertEqual(r.name, 'r')
        self.assertEqual(s.name, 's')
        self.assertEqual(t.name, 't')
        self.assertEqual(u.name, 'u')
        self.assertEqual(p, Sp)
        self.assertEqual(Sp.name, 'S.p')

        self.assertEqual(s, category.CompEq(
            category.Category.ref(g), p,
        ))
        self.assertEqual(u, p)

    def test_sample_theory_hat_mor(self):
        m = self.theory.m
        n = self.theory.n
        X = self.theory.X
        Y = self.theory.Y
        f = self.theory.f
        k = self.theory.k
        i = self.theory.i

        self.assertIsInstance(m, Mor)
        self.assertIsInstance(n, Mor)
        self.assertEqual(m.name, 'm')
        self.assertEqual(n.name, 'n')

        self.assertIs(m.source, X)
        self.assertIs(m.target, Y)
        self.assertIs(n.source, X)
        self.assertIs(n.target, Y)

        self.assertEqual(m, f)

        mhat = m.hat
        self.assertEqual(mhat.ssource, k)
        self.assertEqual(mhat.starget, category.Comp(i, f))
        self.assertEqual(mhat, category.Category.ref(k))

        nhat = n.hat
        self.assertEqual(nhat.ssource, k)
        self.assertEqual(nhat.starget, category.Comp(i, f))
        self.assertEqual(nhat, mhat)

    # TODO: Test raise Error
    def test_obj(self):
        m = MutableTheory.tip()
        m.th.obj('X')
        X: Obj = m.X
        self.assertIsInstance(X, Obj)
        self.assertEqual(X.name, 'X')

    def test_mor(self):
        m = MutableTheory.tip()
        m.th.obj('X')
        m.th.obj('Y')
        X: Obj = m.X
        Y: Obj = m.Y
        m.th.mor('f', X, Y)
        f: Mor = m.f
        self.assertIsInstance(f, Mor)
        self.assertEqual(f.name, 'f')
        self.assertIs(f.source, X)
        self.assertIs(f.target, Y)

        