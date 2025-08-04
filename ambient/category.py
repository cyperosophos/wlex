from ..theory.category import Category as BCategory

class Error:
    pass    

class Obj:
    def __init__(self, typ, name):
        self.typ = typ
        self.name = name

    def check(self, x):
        if x.typ is self:
            return
        raise Error

class Mor:
    source: Obj
    target: Obj

    def __init__(self, typ, name, ksource, ktarget):
        # TODO: What about assigning value to a Mor for which
        # the signature has been provided?
        self.typ = typ
        self.name = name
        self.attrs = dict()
        source_key, source = ksource
        if source_key:
            self.attrs[source_key] = source
        target_key, target = ktarget
        if target_key:
            self.attrs[target_key] = target
        self.source = source
        self.target = target

    def eval(self, x):
        return x.attrs[self]

class Eq:
    source: Mor
    target: Mor

    def __init__(self, typ, name, ksource, ktarget):
        Mor.__init__(self, typ, name, ksource, ktarget)

    def verify(self, x):
        left_side = self.source.eval(x)
        right_side = self.target.eval(x)
        if left_side == right_side:
            return
        raise Error
    
class Comp(Mor):
    def __init__(self, typ, f: Mor, g: Mor, ksource, ktarget):
        super().__init__(typ, None, ksource, ktarget)
        self.f = f
        self.g = g

    def eval(self, x):
        return self.f.eval(self.g.eval(x))
    
class Sub:
    pass
    

class Category:
    def __init__(self, theory):
        self.theory = theory

    def obj_typ(self):
        return

    def obj(self, name):
        setattr(self.theory, name, Obj(self.obj_typ(), name))

    def mor_typ(self):
        return

    def source_key(self):
        return
    
    def target_key(self):
        return

    def mor(self, name, source, target):
        # TODO: Handle triangle
        setattr(self.theory, name, Mor(
            self.mor_typ(),
            name,
            (self.source_key(), source),
            (self.target_key(), target),
        ))

    def eq_typ(self):
        return
    
    def ssource_key(self):
        return
    
    def starget_key(self):
        return

    def eq(self, name, source, target):
        setattr(self.theory, name, Eq(
            self.eq_typ(),
            name,
            (self.ssource_key(), source),
            (self.starget_key(), target)
        ))

    def sub(self, name, theory_cls, **kw):
        setattr(self.theory, name, Sub(theory_cls, kw))

    def compose(self, head, *tail):
        if not tail:
            return head
        return self._compose(head, self.compose(*tail))
    
    def _compose(self, f, g):
        source_key = self.source_key()
        target_key = self.target_key()
        # No further type checking is or should be needed here.
        # Being Composable is the only requirement available for
        # type checking at the lang level.
        if source_key:
            source = source_key.eval(g)
        else:
            source = None

        if target_key:
            target = target_key.eval(f)
        else:
            target = None
        
        return Comp(
            self.mor_typ(),
            f, g,
            (source_key, source),
            (target_key, target),
        )
    
class CheckedCategory(Category):
    backend: BCategory

    def __init__(self, theory, backend: BCategory):
        super().__init__(theory)
        self.backend = backend

    def obj_typ(self):
        return self.backend.Obj

    def mor_typ(self):
        return self.backend.Mor
    
    def source_key(self):
        return self.backend.source
    
    def target_key(self):
        return self.backend.target
    
    def mor(self, name, source, target):
        # TODO: Handle triangle
        BObj = self.backend.Obj
        BObj.check(source)
        BObj.check(target)
        super().mor(name, source, target)

    def eq_typ(self):
        return self.backend.Eq
    
    def ssource_key(self):
        return self.backend.S.source
    
    def starget_key(self):
        return self.backend.S.target

    def eq(self, name, source, target):
        BMor = self.backend.Mor
        BMor.check(source)
        BMor.check(target)
        super().eq(name, source, target)
        _eq = getattr(self.theory, name)
        scond = self.backend.Q.source_globular_cond
        tcond = self.backend.Q.target_globular_cond
        scond.verify(_eq)
        tcond.verify(_eq)
    
    def _compose(self, f, g):
        Composable = self.backend.Composable
        Composable.check(f, g)
        return super()._compose(f, g)