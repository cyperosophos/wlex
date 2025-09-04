import unittest
from wlex.theory import quiver
from wlex.ambient import category, Obj, Mor, Eq

class TestBasicQuiver(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.theory = quiver.BasicQuiver(lambda t: category.Category(t))
        # TODO: For checked ambient just subclass this TestCase with overridden cls.theory.
        # cls.checked_theory = ...

    def test_Node(self):
        Node = self.theory.Node
        self.assertIsInstance(Node, Obj)
        self.assertEqual(Node.name, 'Node')

    def test_Edge(self):
        Edge = self.theory.Edge
        self.assertIsInstance(Edge, Obj)
        self.assertEqual(Edge.name, 'Edge')

    def test_source(self):
        source = self.theory.source
        Edge = self.theory.Edge
        Node = self.theory.Node
        self.assertIsInstance(source, Mor)
        self.assertEqual(source.name, 'source')
        self.assertIs(source.source, Edge)
        self.assertIs(source.target, Node)

    def test_target(self):
        target = self.theory.target
        Edge = self.theory.Edge
        Node = self.theory.Node
        self.assertIsInstance(target, Mor)
        self.assertEqual(target.name, 'target')
        self.assertIs(target.source, Edge)
        self.assertIs(target.target, Node)

    # th = self.theory
    # Node = th.Node
    # Edge = th.Edge
    # source = th.source
    # target = th.target

    # TODO: Test using CheckedCategory as ambient
    # def test_check_Node

class TestQuiver(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.theory = quiver.Quiver(lambda t: category.Category(t))

    def test_Q0(self):
        Q0 = self.theory.Q0
        self.assertIsInstance(Q0, quiver.BasicQuiver)
        self.assertEqual(Q0.Node.name, 'Q0.Node')
        self.assertEqual(Q0.Edge.name, 'Q0.Edge')
        self.assertEqual(Q0.source.name, 'Q0.source')
        self.assertEqual(Q0.target.name, 'Q0.target')

    def test_Q1(self):
        Q1 = self.theory.Q1
        Q0 = self.theory.Q0
        self.assertIsInstance(Q1, quiver.BasicQuiver)
        self.assertEqual(Q1.Node.name, 'Q1.Node')
        self.assertEqual(Q1.Edge.name, 'Q1.Edge')
        self.assertEqual(Q1.source.name, 'Q1.source')
        self.assertEqual(Q1.target.name, 'Q1.target')
        self.assertIs(Q1.Node, Q0.Edge)

    def test_source_globular_cond(self):
        source_globular_cond = self.theory.source_globular_cond
        Q0 = self.theory.Q0
        Q1 = self.theory.Q1
        self.assertIsInstance(source_globular_cond, Eq)
        self.assertEqual(
            source_globular_cond.name,
            'source_globular_cond',
        )
        self.assertEqual(
            source_globular_cond.ssource,
            category.Comp(Q0.source, Q1.source),
        )
        self.assertEqual(
            source_globular_cond.starget,
            category.Comp(Q0.source, Q1.target),
        )
        # Globular condition, namely that source of ssource, etc.
        # are the correct ones, as well as source and target of composition
        # are tested in test_ambient.

    def test_target_globular_cond(self):
        target_globular_cond = self.theory.target_globular_cond
        Q0 = self.theory.Q0
        Q1 = self.theory.Q1
        self.assertIsInstance(target_globular_cond, Eq)
        self.assertEqual(
            target_globular_cond.name,
            'target_globular_cond',
        )        
        self.assertEqual(
            target_globular_cond.ssource,
            category.Comp(Q0.target, Q1.source),
        )
        self.assertEqual(
            target_globular_cond.starget,
            category.Comp(Q0.target, Q1.target),
        )
                
