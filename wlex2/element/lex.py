from ..model.category import Obj, Mor
from ..trusted import lex

class TheoryParallel(Obj):
    def accepts(self, x: object) -> bool:
        return isinstance(x, lex.Parallel) and len(x) == 1

class TheoryParallelI(Mor):
    def ev(self, x: object) -> object:
        assert isinstance(x, lex.Parallel)
        return lex.parallel_i(x)

class TheoryParallelJ(Mor):
    def ev(self, x: object) -> object:
        assert isinstance(x, lex.Parallel)
        return lex.parallel_j(x)

class TheoryEqualizer(Mor):
    def ev(self, x: object) -> object:
        assert isinstance(x, lex.Parallel)
        return lex.equalizer(x)

class TheoryLiftIso(Mor):
    def ev(self, x: object) -> object:
        assert isinstance(x, lex.Fork)
        return lex.lift(x)
