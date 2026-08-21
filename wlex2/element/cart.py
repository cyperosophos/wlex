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

class TheoryDoubleObj(Obj):
    def accepts(self, x: object) -> bool:
        return is_tuple(x) and len(x) == 2

def _is_do(x: object) -> TypeGuard[cart.DoubleObj]:
    if not (is_tuple(x) and len(x) == 2):
        return False

    u, v = x
    return isinstance(u, Obj) and isinstance(v, Obj)

class TheoryDoX(Mor):
    def ev(self, x: object) -> object:
        assert _is_do(x)
        return cart.do_x(x)

class TheoryDoY(Mor):
    def ev(self, x: object) -> object:
        assert _is_do(x)
        return cart.do_y(x)

class TheoryProduct(Mor):
    def ev(self, x: object) -> object:
        assert _is_do(x)
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
