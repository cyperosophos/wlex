from typing import TypeGuard

from ..model.category import Obj, Mor
from ..trusted import category
from .. import is_tuple

class TheoryObj(Obj):
    def accepts(self, x: object) -> bool:
        return isinstance(x, Obj)

class TheoryMor(Obj):
    def accepts(self, x: object) -> bool:
        return isinstance(x, Mor)

class TheorySource(Mor):
    def ev(self, x: object) -> object:
        assert isinstance(x, Mor)
        return category.source(x)

class TheoryTarget(Mor):
    def ev(self, x: object) -> object:
        assert isinstance(x, Mor)
        return category.target(x)

class TheoryIdentity(Mor):
    def ev(self, x: object) -> object:
        assert isinstance(x, Obj)
        return category.identity(x)

class TheoryCompose(Mor):
    def ev(self, x: object) -> object:
        def _is_composable(x: object) -> TypeGuard[category.Composable]:
            if not (is_tuple(x) and len(x) == 2):
                return False

            f, g = x
            return isinstance(f, Mor) and isinstance(g, Mor)

        assert _is_composable(x)
        return category.compose(x)
