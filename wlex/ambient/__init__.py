from .cells import Obj, Mor, Eq


class Checked:
    unchecked_cls: type

    def __init__(self, theory, backend, *args, **kwargs):
        self.unchecked = self.unchecked_cls(theory, *args, **kwargs)
        self.backend = backend