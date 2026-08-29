from abc import ABCMeta, abstractmethod
from typing import TypeGuard, Iterable, Iterator

from .category import Obj, Mor, Param
from . import WithItems
from .. import is_tuple

def _all_mor(x: list[tuple[str, Mor] | None]) -> TypeGuard[list[tuple[str, Mor]]]:
    return all(m is not None for m in x)

class BaseSpan(WithItems[Mor], metaclass=ABCMeta):
    __slots__ = ()

    @abstractmethod
    def param(self) -> Param:
        pass

    def __eq__(self, x: object):
        # This is needed in `private.is_terminal_mor`
        return self is x or (
            isinstance(x, type(self))
            and super().__eq__(x)
            and self.param() == x.param()
        )

class Span(BaseSpan):
    __slots__ = ('components', 'labels')
    components: tuple[Mor, ...]
    labels: tuple[str, ...]

    def __init__(self, components: Iterable[Mor], labels: Iterable[str]):
        self.labels = tuple(labels)
        self.components = tuple(components)
        if len(self.labels) != len(self.components):
            raise ValueError("Labels and components must have the same length.")

    def __len__(self):
        return len(self.components)

    def getitem(self, idx: int):
        return self.components[idx]

    def param(self):
        return Param((
            (l, c.target) if l else c.target
            for l, c in zip(self.labels, self.components)
        ))

    def __eq__(self, x: object):
        return self is x or (
            isinstance(x, type(self))
            and self.components == x.components
            and self.labels == x.labels
        )

class Product(Obj, BaseSpan):
    __slots__ = ('components', 'frozen', 'label_to_idx_map')
    components: list[Obj]
    frozen: bool
    label_to_idx_map: dict[str, int]

    @classmethod
    def is_terminal(cls, obj: Obj):
        return isinstance(obj, cls) and not obj.components

    def label_to_idx(self, label: str):
        return self.label_to_idx_map[label]

    def idx_to_label(self, idx: int):
        # Check that idx is within range
        if idx < 0 or idx >= len(self):
            raise ValueError('Index out of range')

        # Linear time!
        for k, v in self.label_to_idx_map.items():
            if v == idx:
                break
        else:
            raise ValueError('No label for index')

        return k

    def accepts(self, x: object):
        return (
            is_tuple(x)
            and len(self.components) == len(x)
            and all(
                c.accepts(xc)
                for c, xc in zip(self.components, x)
            )
        )

    def __eq__(self, x: object):
        # This is needed in `private.is_terminal_mor`
        return self is x or (
            isinstance(x, type(self))
            and self.components == x.components
            and self.label_to_idx_map == x.label_to_idx_map
        )

    def getitem(self, idx: int) -> Mor:
        return Projection(self, idx)

    def __len__(self):
        return len(self.components)

    @classmethod
    def _reuse_first(
        cls, components: Iterator[Obj],
    ) -> tuple[list[Obj], dict[str, int], bool]:
        for component in components:
            if isinstance(component, Product) and not component.frozen:
                res = (component.components, component.label_to_idx_map, True)
                del component.components
                del component.label_to_idx_map
                return res

            return [component], {}, False

        return [], {}, False

    def __init__(self, param: Param):
        super().__init__()
        it = iter(param.components)
        comps, li_map, is_reusing = self._reuse_first(it)

        param_li = param.label_to_idx_map
        if is_reusing:
            idx_offset = len(comps) - 1
        else:
            idx_offset = 0

        for l, i in param_li:
            # Repeated labels are allowed because otherwise we wouldn't have a param -> product function.
            if is_reusing and i == 0:
                raise ValueError("Reused component can't be labeled")

            li_map[l] = i + idx_offset

        # Single product component is allowed. This is required by the variadic product.
        comps.extend(it)
        self.frozen = True
        self.components = comps
        self.label_to_idx_map = li_map

    def pairing_components(self, components: Iterable[tuple[str, Mor] | Mor]):
        res: list[tuple[str, Mor] | None] = [None]*len(self.components)

        for i, lc in enumerate(components):
            if isinstance(lc, tuple):
                l, c = lc
                i = self.label_to_idx(l)
            else:
                c = lc
                l = ''

            if res[i] is not None:
                raise ValueError("Conflicting label or index")

            res[i] = (l, c)

        if not _all_mor(res):
            raise ValueError("Not enough components for target")

        return res

class Projection(Mor):
    __slots__ = ('idx',)
    idx: int

    def __init__(self, source: Product, idx: int):
        target = source.components[idx]
        super().__init__(source, target)
        self.idx = idx
        self.name = f'${idx}'

    def ev(self, x: object):
        assert is_tuple(x)
        return x[self.idx]

    def reduce(self, mor: Mor):
        if isinstance(mor, Pairing):
            return mor.components[self.idx]

        return None

    def __eq__(self, x: object):
        return self is x or (
            isinstance(x, type(self))
            and self.source == x.source
            and self.idx == x.idx
        )

class Pairing(Mor):
    __slots__ = ('components', 'frozen')
    components: list[Mor]
    frozen: bool

    def ev(self, x: object):
        return tuple(c.ev(x) for c in self.components)

    def __eq__(self, x: object):
        if self is x:
            return True

        if not (
            isinstance(x, type(self))
            and self.components == x.components
            and (True if self.components else self.source == x.source)
        ):
            return False

        # This is what remains in order to ensure that targets are equal.
        target = self.target
        xtarget = x.target
        assert isinstance(target, Product)
        assert isinstance(xtarget, Product)
        return target.label_to_idx == xtarget.label_to_idx

    @classmethod
    def _reuse_first(cls, components: Iterator[Mor]) -> tuple[Obj, list[Mor]]:
        for component in components:
            source = component.source
            if isinstance(component, Pairing) and not component.frozen:
                res = component.components
                del component.components
                return source, res

            return source, [component]

        raise ValueError("Can't have empty component list")

    def __init__(self, components: Iterable[Mor] | Obj, target: Product):
        # Span check is done in `proven`.
        if isinstance(components, Obj):
            source = components
            comps: list[Mor] = []
        else:
            it = iter(components)
            source, comps = self._reuse_first(it)
            comps.extend(it)

        super().__init__(source, target)
        self.components = comps
        self.frozen = True
