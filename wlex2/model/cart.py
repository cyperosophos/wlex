from abc import ABCMeta, abstractmethod
from typing import TypeVar, TypeGuard, Iterable, Iterator

from .category import Obj, Mor
from . import WithItems

def _all_mor(x: list[Mor | None]) -> TypeGuard[list[Mor]]:
    return all(m is not None for m in x)

T = TypeVar('T')
Components = Iterable[tuple[str, T] | T]

class Product(Obj, WithItems[Mor]):
    __slots__ = 'components', 'frozen', 'label_to_idx_map'
    components: list[Obj]
    frozen: bool
    label_to_idx_map: dict[str, int]

    def param(self) -> Components[Obj]:
        idx_to_label: dict[int, str] = {}
        for k, v in self.label_to_idx_map.items():
            idx_to_label[v] = k

        for i, c in enumerate(self.components):
            label = idx_to_label.get(i)
            if label:
                yield label, c

            yield c

    @staticmethod
    def is_product_acceptable(x: object) -> TypeGuard[tuple[object]]:
        return isinstance(x, tuple)

    def accepts(self, x: object):
        return (
            self.is_product_acceptable(x)
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
        cls, components: Iterator[tuple[str, Obj] | Obj],
    ) -> tuple[list[Obj], dict[str, int]]:
        for component in components:
            if isinstance(component, tuple):
                label, component = component
            else:
                label = ''

            if isinstance(component, Product) and not component.frozen:
                if label:
                    raise ValueError("Component to be reused can't be labeled.")

                res = (component.components, component.label_to_idx_map)
                del component.components
                del component.label_to_idx_map
                return res

            label_map: dict[str, int] = {}
            if label:
                label_map[label] = 0

            return [component], label_map

        return [], {}

    def __init__(self, components: Components[Obj]):
        super().__init__()
        it = iter(components)
        comps, label_to_idx_map = self._reuse_first(it)

        for i, component in enumerate(it):
            if isinstance(component, tuple):
                label, component = component
            else:
                label = ''

            comps.append(component)
            if label:
                label_to_idx_map[label] = i + 1

        self.frozen = True
        self.components = comps
        self.label_to_idx_map = label_to_idx_map

    # @staticmethod
    # def extract_labels(components: Components[Obj]):
    #     labels: dict[str, int] = {}
    #     comps: list[Obj] = []
    #     for i, lc in enumerate(components):
    #         if isinstance(lc, tuple):
    #             l, c = lc
    #             if l in labels:
    #                 raise ValueError("Repeated label")

    #             labels[l] = i
    #         else:
    #             c = lc

    #         comps.append(c)

    #     return labels, tuple(comps)

    # def set_labels(self, map_: dict[str, int]):
    #     self.label_to_idx_map = map_

    def label_to_idx(self, label: str):
        return self.label_to_idx_map[label]

    def idx_to_label(self, idx: int):
        _ = self.components[idx] # Check that idx is within range

        # Linear time!
        for k, v in self.label_to_idx_map.items():
            if v == idx:
                break
        else:
            raise ValueError('No label for index')

        return k

    def fix_order(self, components: Components[Mor]):
        res: list[Mor | None] = [None]*len(self.components)

        for i, lc in enumerate(components):
            if isinstance(lc, tuple):
                l, c = lc
                i = self.label_to_idx(l)
            else:
                c = lc

            if res[i] is not None:
                raise ValueError("Conflicting label or index")

            res[i] = c

        if not _all_mor(res):
            raise ValueError("Not enough components for target")

        return tuple(res)

class Projection(Mor): # TODO: Probably use this as base for LabeledProjection
    __slots__ = ('idx',)
    idx: int

    def __init__(self, source: Product, idx: int):
        target = source.components[idx]
        super().__init__(source, target)
        self.idx = idx
        self.name = f'${idx}'

    def ev(self, x: object):
        source = self.source
        assert isinstance(source, Product)
        assert Product.is_product_acceptable(x)
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

class BasePairing(WithItems[Obj], metaclass=ABCMeta):
    __slots__ = ()

    @property
    @abstractmethod
    def mor(self) -> Mor:
        pass

    def getitem(self, idx: int) -> Obj:
        target = self.mor.target
        assert isinstance(target, Product)
        return target.components[idx]

    def __len__(self):
        target = self.mor.target
        assert isinstance(target, Product)
        return len(target.components)

    def __eq__(self, x: object):
        return self is x or (
            isinstance(x, type(self))
            and self.mor == x.mor
        )

class AbstractPairing(BasePairing):
    __slots__ = ('_mor',)
    _mor: Mor

    @property
    def mor(self):
        return self._mor

    def __init__(self, mor: Mor):
        if not isinstance(mor.target, Product):
            raise ValueError('`target` must be product.')

        self._mor = mor

class Pairing(Mor, BasePairing):
    __slots__ = ('components', 'frozen')
    components: list[Mor]
    frozen: bool

    def param(self):
        target = self.target
        assert isinstance(target, Product)
        return target.param()

    @property
    def mor(self):
        return self

    def ev(self, x: object):
        return tuple(c.ev(x) for c in self.components)

    def __eq__(self, x: object):
        return self is x or (
            isinstance(x, type(self))
            and self.source == x.source
            and self.components == x.components
        )

    @classmethod
    def _reuse_first(cls, components: Iterator[Mor]) -> tuple[Obj, list[Mor]]:
        for component in components:
            source = component.source
            if isinstance(component, Pairing) and not component.frozen:
                res = component.components
                del component.components
                assert isinstance(res, list)
                return source, res

            return source, [component]

        raise ValueError("Can't have empty component list")

    def __init__(self, components: Iterable[Mor] | Obj):
        # Span check is done in `proven`.
        if isinstance(components, Obj):
            source = components
            comps: list[Mor] = []
            target = Product(())
        else:
            it = iter(components)
            source, comps = self._reuse_first(it)
            comps.extend(it)
            target = Product(c.target for c in comps)

        super().__init__(source, target)
        self.components = comps
        self.frozen = True
