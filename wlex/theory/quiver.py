from ..ambient import Obj, Mor, Eq

class BasicQuiver:
    Node: Obj
    Edge: Obj

    source: Mor
    target: Mor

    def __init__(self, ambient):
        from ..ambient.category import Category

        th: Category = ambient(self)
        th.obj('Node')
        th.obj('Edge')
        Node = self.Node
        Edge = self.Edge

        th.mor('source', Edge, Node)
        th.mor('target', Edge, Node)

class Quiver:
    Q0: BasicQuiver
    Q1: BasicQuiver

    source_globular_cond: Eq
    target_globular_cond: Eq

    def __init__(self, ambient):
        from ..ambient.category import Category

        th: Category = ambient(self)
        c = th.compose
        th.sub('Q0', BasicQuiver)
        Q0 = self.Q0
        th.sub('Q1', BasicQuiver, Node=Q0.Edge)
        Q1 = self.Q1

        th.eq(
            'source_globular_cond',
            c(Q0.source, Q1.source),
            c(Q0.source, Q1.target),
        )

        th.eq(
            'target_globular_cond',
            c(Q0.target, Q1.source),
            c(Q0.target, Q1.target),
        )
        

