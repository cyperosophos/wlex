import unittest

from wlex.theory import quiver
from wlex.ambient.category import OnceStub as _s, Once as _o
from wlex.ambient.cells import named
from wlex.ambient.cells.category import (
    CategoryTypeObj as T, CategoryPrimEv as M, CategoryAxiom as E,
)
from wlex.primitive import quiver as prim

class TestBasicQuiver(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        stub = _s(quiver.BasicQuiverStub(
            Node=_o(T(prim.Node)),
            Edge=_o(T(prim.Edge)),
            source=_o(M(prim.source)),
            target=_o(M(prim.target)),
        ))
        cls.theory = quiver.BasicQuiverTheory.from_ctx(
            quiver.BasicQuiver(stub),
        )

    def test_theory(self):
        from wlex.ambient.cells import category

        th = self.theory

        self.assertIsInstance(th.Node, category.CategoryObj)
        self.assertIsInstance(th.Edge, category.CategoryObj)
        self.assertIsInstance(th.source, category.CategoryMor)
        self.assertIsInstance(th.target, category.CategoryMor)
        self.assertTrue(th.source.source.identical(th.Edge))
        self.assertTrue(th.source.target.identical(th.Node))
        self.assertTrue(th.target.source.identical(th.Edge))
        self.assertTrue(th.target.target.identical(th.Node))

    def test_execution(self):
        from wlex.ambient import cells

        class A:
            pass

        class B:
            pass

        def edge_ev(x: object):
            assert False

        th = self.theory
        source = named('source', cells.TypeObj(A))
        target = named('target', cells.TypeObj(B))
        edge = named('edge', cells.PrimMor(source, target, edge_ev)) # We don't execute this

        self.assertTrue(th.Node.accepts(source))
        self.assertTrue(th.Edge.accepts(edge))
        self.assertFalse(th.Edge.accepts(target))
        self.assertFalse(th.Node.same(source, target))
        self.assertTrue(th.Node.same(target, target))

        self.assertIs(th.source.public_ev(edge), source)
        self.assertIs(th.target.public_ev(edge), target)
        self.assertRaises(cells.SourceMismatch, th.source.public_ev, 0)

        d_source = th.source.public_ev(
            cells.Defensive.enter(edge, th.source),
        )
        d_target = th.target.public_ev(
            cells.Defensive.enter(edge, th.target),
        )
        assert isinstance(d_source, cells.Defensive)
        assert isinstance(d_target, cells.Defensive)
        self.assertIs(d_source.value, source)
        self.assertIs(d_target.value, target)

        # TODO: Test erroneous th.source, th.target with defensive

class TestQuiver(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        stub = _s(quiver.QuiverStub(
            Q0=_s(quiver.BasicQuiverStub(
                Node=_o(T(prim.Node)),
                Edge=_o(T(prim.Edge)),
                source=_o(M(prim.source)),
                target=_o(M(prim.target)),
            )),
            Q1=_s(quiver.BasicQuiverStub(
                Node=_o(),
                Edge=_o(T(prim.Q1Edge)),
                source=_o(M(prim.Q1_source)),
                target=_o(M(prim.Q1_target)),
            )),
            # `public` means that it must be checked when type checking the
            # argument of `public_ev` (`ev` does not type-check its argument).
            source_globular_cond=_o(E(True)),
            target_globular_cond=_o(E(True)),
        ))
        cls.theory = quiver.QuiverTheory.from_ctx(
            quiver.Quiver(stub)
        )

    def test_theory(self):
        from wlex.ambient.cells import category

        th = self.theory

        self.assertIsInstance(th.Q0.Node, category.CategoryObj)
        self.assertIsInstance(th.Q0.Edge, category.CategoryObj)
        self.assertIsInstance(th.Q0.source, category.CategoryMor)
        self.assertIsInstance(th.Q0.target, category.CategoryMor)
        self.assertIs(th.Q1.Node, th.Q0.Edge)
        self.assertIsInstance(th.Q1.Edge, category.CategoryObj)
        self.assertIsInstance(th.Q1.source, category.CategoryMor)
        self.assertIsInstance(th.Q1.target, category.CategoryMor)

    def test_execution(self):
        from wlex.ambient import cells

        class A:
            pass

        class B:
            pass

        def edge_ev(x: object):
            assert False

        th = self.theory
        source = named('source', cells.TypeObj(A))
        target = named('target', cells.TypeObj(B))
        Q1_source = named('Q1_source', cells.PrimMor(source, target, edge_ev))
        Q1_target = named('Q1_target', cells.PrimMor(source, target, edge_ev))
        Q1_edge = cells.PrimEq(Q1_source, Q1_target, False)

        self.assertTrue(th.Q0.Node.accepts(source))
        self.assertTrue(th.Q0.Edge.accepts(Q1_source))
        self.assertFalse(th.Q0.Edge.accepts(Q1_edge))
        self.assertTrue(th.Q1.Edge.accepts(Q1_edge))
        self.assertFalse(th.Q1.Edge.accepts(Q1_target))
        self.assertFalse(th.Q0.Node.same(source, target))
        self.assertTrue(th.Q0.Node.same(target, target))
        self.assertFalse(th.Q1.Node.same(Q1_source, Q1_target))
        self.assertTrue(th.Q1.Node.same(Q1_target, Q1_target))

        self.assertIs(th.Q0.source.public_ev(Q1_source), source)
        self.assertIs(th.Q0.target.public_ev(Q1_target), target)
        self.assertRaises(cells.SourceMismatch, th.Q0.source.public_ev, 0)
        self.assertIs(th.Q1.source.public_ev(Q1_edge), Q1_source)
        self.assertIs(th.Q1.target.public_ev(Q1_edge), Q1_target)
        self.assertRaises(cells.SourceMismatch, th.Q1.source.public_ev, 0)

        d_source = th.Q0.source.public_ev(
            cells.Defensive.enter(Q1_source, th.Q0.source),
        )
        d_target = th.Q0.target.public_ev(
            cells.Defensive.enter(Q1_source, th.Q0.target),
        )
        assert isinstance(d_source, cells.Defensive)
        assert isinstance(d_target, cells.Defensive)
        self.assertIs(d_source.value, source)
        self.assertIs(d_target.value, target)

