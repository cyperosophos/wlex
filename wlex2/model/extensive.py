from typing import Iterable, Iterator, NamedTuple, Sequence

from .category import Obj, Mor
from .cart import Product
from . import WithItems

class Shadowed(NamedTuple):
    idx: int
    value: object

class Coproduct(Obj, WithItems[Mor]):
    __slots__ = ('components', 'frozen')
    components: list[Obj]
    frozen: bool

    @classmethod
    def _reuse_first(cls, components: Iterator[Obj]) -> list[Obj]:
        for component in components:
            if isinstance(component, Coproduct) and not component.frozen:
                res = component.components
                del component.components
                return res

            return [component]

        return []

    def __init__(self, components: Sequence[Obj]):
        # We use Sequence instead of Iterable for checking only length in `proven`.
        super().__init__()
        it = iter(components)
        comps = self._reuse_first(it)
        comps.extend(it)
        self.components = comps
        self.frozen = True

    def getitem(self, idx: int) -> Mor:
        return Coprojection(self, idx)

    def __len__(self):
        return len(self.components)

    def accepts(self, x: object):
        # Handle shadowed components
        if isinstance(x, Shadowed):
            return self.components[x.idx].accepts(x.value)

        # Terminal object accepts all values, so we handle it differently.
        return any(
            x == i if Product.is_terminal(c) else c.accepts(x)
            for i, c in enumerate(self.components)
        )

    def __eq__(self, x: object):
        return self is x or (
            isinstance(x, type(self))
            and self.components == x.components
        )

class Coprojection(Mor):
    __slots__ = ('idx',)
    idx: int

    def __init__(self, target: Coproduct, idx: int):
        source = target.components[idx]
        super().__init__(source, target)
        self.idx = idx
        self.name = f'!{idx}'

    def ev(self, x: object):
        return x

    # `reduce` is handled in copairing

    def __eq__(self, x: object):
        return self is x or (
            isinstance(x, type(self))
            and self.target == x.target
            and self.idx == x.idx
        )

class Copairing(Mor):
    __slots__ = ('components', 'frozen')
    components: list[Mor]
    frozen: bool

    def reduce(self, mor: Mor):
        if isinstance(mor, Coprojection):
            return self.components[mor.idx]

        # TODO: Reduce with split when this is a stick.

        return None

    def ev(self, x: object):
        if isinstance(x, Shadowed):
            return self.components[x.idx].ev(x.value)

        if isinstance(x, int):
            c = self.components[x]
            if Product.is_terminal(c.source):
                return c.ev(x)

        for c in self.components:
            if c.source.accepts(x):
                return c.ev(x)

        raise ValueError("Can't evaluate")

    def __ev__(self, x: object):
        return self is x or (
            isinstance(x, type(self))
            and self.components == x.components
            and (True if self.components else self.target == x.target)
        )

    @classmethod
    def _reuse_first(cls, components: Iterator[Mor]) -> tuple[Obj, list[Mor]]:
        for component in components:
            target = component.target
            if isinstance(component, Copairing) and not component.frozen:
                res = component.components
                del component.components
                return target, res

            return target, [component]

        raise ValueError("Can't have empty component list")

    def __init__(self, components: Iterable[Mor] | Obj, source: Coproduct):
        if isinstance(components, Obj):
            target = components
            comps: list[Mor] = []
        else:
            it = iter(components)
            target, comps = self._reuse_first(it)
            comps.extend(it)

        super().__init__(source, target)
        self.components = comps
        self.frozen = True

class Split(Mor):
    __slots__ = ('frozen',)
    # `reduce` with copairing corresponding to stick.
    # Take into account that by evaluating negation (an isomorphism)
    # on the requirement one gets an equivalent requirement, which may
    # actually the requirement to check for the purposes of reducing.

    def __init__(self, mor: Mor):
        # This has to be variadic!!
        source = mor.source
        target = Coproduct((

        ))