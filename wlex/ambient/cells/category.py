from .. import cells

class Obj(cells.Obj):
    def identity(self):
        from ..category import Id
        return Id(self)

class PrimObj(cells.PrimObj, Obj):
    pass