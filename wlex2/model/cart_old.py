from abc import ABCMeta, abstractmethod
from typing import TypeGuard, Iterable, Iterator
from collections.abc import Sized

from .category import Obj, Mor, Param
from . import WithItems
from .. import is_tuple

def _all_mor(x: list[Mor | None]) -> TypeGuard[list[Mor]]:
    return all(m is not None for m in x)

class BaseSpan(WithItems[Mor], metaclass=ABCMeta):
    __slots__ = ('label_to_idx_map',)
    label_to_idx_map: dict[str, int]

    @abstractmethod
    def unlabeled_param(self) -> Iterable[Obj]:
        pass

    def param(self):
        def _gen_components():
            idx_to_label: dict[int, str] = {}
            for k, v in self.label_to_idx_map.items():
                idx_to_label[v] = k

            for i, c in enumerate(self.unlabeled_param()):
                label = idx_to_label.get(i)
                if label:
                    yield label, c
                else:
                    yield c

        return Param(_gen_components())

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

    def __eq__(self, x: object):
        # This is needed in `private.is_terminal_mor`
        return self is x or (
            isinstance(x, type(self))
            and super().__eq__(x)
            and self.label_to_idx_map == x.label_to_idx_map
        )

class Span(BaseSpan):
    __slots__ = ('_components',)
    _components: tuple[Mor, ...]

    def __init__(self, components: Iterable[tuple[str, Mor] | Mor]):
        # param is inferred from components. Therefore less checking is required
        # in `proven`.
        li_map: dict[str, int] = {}
        comps: list[Mor] = []

        for i, c in enumerate(components):
            if isinstance(c, tuple):
                label, c = c
            else:
                label = ''

            comps.append(c)
            if label:
                li_map[label] = i

        self.label_to_idx_map = li_map
        self._components = tuple(comps)

    def __len__(self):
        return len(self._components)

    def getitem(self, idx: int):
        return self._components[idx]

    def unlabeled_param(self):
        return (m.target for m in self._components)

class Product(Obj, BaseSpan):
    __slots__ = ('components', 'frozen')
    components: list[Obj]
    frozen: bool

    def unlabeled_param(self):
        return self.components

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

    def __init__(self, components: Components[Obj], _allow_single_component: bool = False):
        super().__init__()
        it = iter(components)
        comps, li_map = self._reuse_first(it)

        for i, component in enumerate(it):
            if isinstance(component, tuple):
                label, component = component
            else:
                label = ''

            comps.append(component)
            if label:
                # TODO: Index offset based on reused component!
                li_map[label] = i + 1

        self.frozen = True
        self.components = comps
        self.label_to_idx_map = li_map

    # TODO: Define strict? for case of one component with no label.
    # Check that this works with pairing! Instead make sure there is no
    # single component during initialization.

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

class Projection(Mor):
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

class BasePairing(Sized, metaclass=ABCMeta):
    __slots__ = ()

    @property
    @abstractmethod
    def mor(self) -> Mor:
        pass

    def param(self):
        target = self.mor.target
        return target.param()

    def __eq__(self, x: object):
        return self is x or (
            isinstance(x, type(self))
            and self.mor == x.mor
        )

    def __len__(self):
        target = self.mor.target
        if isinstance(target, Product):
            return len(target)

        return 1

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

    @property
    def mor(self):
        return self

    def ev(self, x: object):
        return tuple(c.ev(x) for c in self.components)

    def __eq__(self, x: object):
        if self is x:
            return True

        if not (
            isinstance(x, type(self))
            and self.source == x.source
            and self.components == x.components
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
