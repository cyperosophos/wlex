from typing import TypeGuard, Sequence

from ..model.category import Obj, Mor
from ..trusted import cart
from .. import is_tuple

class TheoryTerminal(Mor):
    def ev(self, x: object) -> object:
        return cart.terminal()

class TheoryTerminalMorIso(Mor):
    def ev(self, x: object) -> object:
        assert isinstance(x, Obj)
        return cart.terminal_mor(x)

class TheoryParam(Obj):
    def accepts(self, x: object) -> bool:
        return is_tuple(x) and len(x) == 2

def _is_param(x: object) -> TypeGuard[cart.Param]:
    if not (is_tuple(x) and len(x) == 2):
        return False

    u, v = x
    return isinstance(u, Obj) and isinstance(v, Obj)

class TheoryParamX(Mor):
    def ev(self, x: object) -> object:
        assert _is_param(x)
        return cart.param_x(x)

class TheoryParamY(Mor):
    def ev(self, x: object) -> object:
        assert _is_param(x)
        return cart.param_y(x)

class TheoryProduct(Mor):
    def ev(self, x: object) -> object:
        assert _is_param(x)
        return cart.product(x)

class TheoryPairingIso(Mor):
    def ev(self, x: object) -> object:
        def _is_sequence(x: object) -> TypeGuard[Sequence[object]]:
            return isinstance(x, Sequence)

        def _is_span(x: object) -> TypeGuard[cart.Span]:
            return _is_sequence(x) and all(
                isinstance(i, Mor) for i in x
            )

        assert _is_span(x)
        return cart.pairing(x)
