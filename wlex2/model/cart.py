from abc import ABCMeta, abstractmethod
from typing import Iterable, Callable, TypeGuard, TypeVar
import weakref

from .category import Obj, Mor, eq_with_length, Composition, ProjError
from .. import is_tuple

T = TypeVar('T')
WRef = Callable[[], 'T | None']

class NullParam:
    __slots__ = ('terminal',)
    terminal: WRef['Terminal']

    def __init__(self):
        # One takes care at a higher level that tis gets only instantiated once.
        self.terminal = lambda: None

class BaseNullSpan(metaclass=ABCMeta):
    __slots__ = ()
    par: NullParam

    @abstractmethod
    def obj(self) -> Obj:
        pass

    def __eq__(self, x: object):
        return self is x or (
            isinstance(x, type(self))
            and self.obj() == x.obj()
            and self.par == x.par
        )

class NullSpan(BaseNullSpan):
    __slots__ = ('_obj', 'par')
    _obj: Obj
    par: NullParam

    def obj(self):
        return self._obj

    def __init__(self, obj: Obj, par: NullParam):
        self._obj = obj
        self.par = par

class Terminal(Obj, BaseNullSpan):
    __slots__ = ('par',)
    par: NullParam

    def obj(self):
        return self

    def __new__(cls, par: NullParam):
        res = par.terminal()
        if res is None:
            return super().__new__(cls)

        return res

    def __init__(self, par: NullParam):
        if par.terminal() is not None:
            return

        super().__init__()
        par.terminal = weakref.ref(self)
        self.par = par

    def accepts(self, x: object) -> bool:
        return x is ()

class TerminalMor(Mor):
    __slots__ = ()

    def __init__(self, span: BaseNullSpan):
        # par gets recovered from target
        super().__init__(span.obj(), Terminal(span.par))

    def ev(self, x: object):
        return ()

    def reduce(self, mor: Mor):
        t = self.target
        assert isinstance(t, Terminal)
        return TerminalMor(NullSpan(mor.source, t.par))

    def __hash__(self):
        return hash(self.source)

    # @property
    # def par(self):
    #     t = self.target
    #     assert isinstance(t, Terminal)
    #     return t.par

def _all_t[T](x: list[T | None]) -> TypeGuard[list[T]]:
    return all(m is not None for m in x)

class Param:
    __slots__ = ('x', 'y', 'label', 'product')
    x: Obj
    y: Obj
    label: str
    product: WRef['Product']

    def __init__(self, x: Obj, y: Obj, label: str):
        if isinstance(x, Product):
            if label in x.labels:
                raise ValueError('Repeated label')

        self.x = x
        self.y = y
        self.label = label
        self.product = lambda: None

class BaseSpan(metaclass=ABCMeta):
    __slots__ = ()
    par: Param

    @abstractmethod
    def p(self) -> Mor:
        pass

    @abstractmethod
    def q(self) -> Mor:
        pass

    def __eq__(self, x: object):
        return self is x or (
            isinstance(x, type(self))
            and self.p() == x.p()
            and self.q() == x.q()
            and self.par == x.par
        )

class Span(BaseSpan):
    __slots__ = ('_p', '_q', 'par')
    _p: Mor
    _q: Mor

    def __init__(self, p: Mor, q: Mor, par: Param):
        # This has to be checked in proven
        self._p = p
        self._q = q
        self.par = par

    def p(self):
        return self._p

    def q(self):
        return self._q

class Product(Obj, BaseSpan):
    __slots__ = ('components', 'length', 'labels', 'par')
    components: list[Obj]
    length: int
    labels: dict[str, int]
    # TODO: Check where components is being used since length bound needs
    # to be taken into account. Same applies to Pairing.components and
    # Equalizer.requirements.

    def pack(self):
        # Specifically supports only the product of terminal with an object
        # (but not the product of an object with terminal).
        source = self.components[0]
        t = self.par.x
        if not(
            isinstance(t, Terminal)
            and self.par.y == source
        ):
            raise ProjError

        return Pairing(Span(
            TerminalMor(NullSpan(source, t.par)),
            Composition(source),
            self.par,
        ))

    def component(self, idx: int):
        if idx >= self.length:
            raise ValueError("Out of range")

        return self.components[idx]

    def proj(self, target: Obj | tuple[int, ...], _depth: int = 1):
        try:
            return super().proj(target)
        except ProjError:
            pass

        if isinstance(target, tuple):
            if _depth >= len(target):
                return Projection(self, target[-1])

            h = Projection(self, target[_depth-1])
            return Composition.strict(
                h.target.proj(target, _depth=_depth+1),
                h,
            )

        assert isinstance(target, Product)
        # Just as with inclusion, since the target is already given,
        # we can manually create the needed pairing here.
        # The components are projections in the order required by target.
        # TODO: Since Pairing will be overloaded reconsider how it's being used in trusted.
        idx_to_label = ['']*self.length
        for l, i in self.labels.items():
            idx_to_label[i] = l

        idxs = target.pairing_components((
            (idx_to_label[i], i)
            for i in range(self.length)
        ), _shrink=True)

        projs: list[Mor] = [Projection(self, i) for i in idxs]
        # Projections have to be postcomposed with more projetions.
        # TODO: !!! Ax(B + C) ~= AxB + AxC
        # The full normalization ends up being something like Equalizer(Coproduct(Product()))
        # (and one has to consider W-Types as infinite coproducts).
        # One should then probably have a minimal version Parallel and Param,
        # and then subclass them in context.
        projs = [
            Composition.strict(
                p.target.proj(target.components[i]),
                p,
            )
            for i, p in enumerate(projs)
        ]
        return Pairing((projs, target))

    def _tail_proj(self, target: Obj) -> Mor:
        if isinstance(target, Terminal):
            return TerminalMor(NullSpan(self, target.par))

        if not isinstance(target, Product):
            return Projection(self, 0)

        # target can be a product of length 1.
        # In which case, the original single component product used in the Param
        # gets returned.

        return Pairing(Span(
            self._tail_proj(target.par.x),
            Projection(self, len(target.components) - 1), # This component doesn't get flattened
            target.par,
        ))

    def p(self):
        # Notice that Pairing(self) is the identity.
        return self._tail_proj(self.par.x)

    def q(self):
        return Projection(self, self.length - 1)

    def label_to_idx(self, label: str):
        idx = self.labels[label]
        if idx >= self.length:
            raise ValueError("Not a label of this product")

        return idx

    # def idx_to_label(self, idx: int):
    #     # Check that idx is within range
    #     if idx < 0 or idx >= self.length:
    #         raise ValueError('Index out of range')

    #     # Linear time!
    #     for k, v in self.labels.items():
    #         if v == idx:
    #             break
    #     else:
    #         raise ValueError('No label for index')

    #     return k

    def accepts(self, x: object):
        return (
            is_tuple(x)
            and self.length == len(x)
            and all(
                c.accepts(xc)
                for c, xc, _ in zip(self.components, x, range(self.length))
            )
        )

    @classmethod
    def _first_components(cls, component: Obj) -> tuple[list[Obj], dict[str, int]]:
        if isinstance(component, Product):
            components = component.components
            li_map = component.labels
            if component.length == len(components):
                return components, li_map

            return components[:], li_map.copy()

        if isinstance(component, Terminal):
            return [], {}

        return [component], {}

    def __new__(cls, par: Param):
        res = par.product()
        if res is None:
            return super().__new__(cls)

        return res

    def __init__(self, par: Param):
        if par.product() is not None:
            return

        par.product = weakref.ref(self)
        super().__init__()
        components, li_map = self._first_components(par.x)
        li_map[par.label] = len(components)
        components.append(par.y)
        self.length = len(components)
        self.components = components
        self.labels = li_map

    def pairing_components[T](
        self,
        components: Iterable[tuple[str, T]],
        _shrink: bool = False,
    ):
        length = self.length
        # The label is not needed since `self` is the target.
        res: list[T | None] = [None]*length
        count = 0
        for i, (l, c) in enumerate(components):
            if l:
                i = self.label_to_idx(l)

            if _shrink and i >= length:
                if count >= length:
                    break

                continue

            if res[i] is not None:
                raise ValueError("Conflicting label or index")

            res[i] = c
            count += 1

        if not _all_t(res):
            raise ValueError("Not enough components for target")

        assert count == length
        return res

class Projection(Mor):
    __slots__ = ('idx',)
    idx: int

    def __init__(self, source: Product, idx: int):
        if idx >= source.length:
            raise ValueError("idx out of range")

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

    def __hash__(self):
        return hash((self.source, self.idx))

class Pairing(Mor):
    __slots__ = ('components', 'length')
    components: list[Mor]
    length: int

    def ev(self, x: object):
        return tuple(c.ev(x) for c in self.components)

    def __eq__(self, x: object):
        return self is x or (
            isinstance(x, Pairing)
            and self.target == x.target # Same labels
            and self.length == x.length
            and eq_with_length(
                self.components, self.length,
                x.components, x.length,
            )
        )

    @classmethod
    def _first_components(cls, component: Mor) -> list[Mor]:
        if isinstance(component, Pairing):
            components = component.components
            if component.length == len(components):
                return components

            return components[:]

        if isinstance(component, TerminalMor):
            return []

        return [component]

    def __init__(self, span: BaseSpan | tuple[list[Mor], Product]):
        if isinstance(span, tuple):
            components, target = span
            source = components[0].source
        else:
            # Span check is done in `proven`.
            p = span.p()
            q = span.q()
            source = p.source
            target = Product(span.par)
            components = self._first_components(p)
            components.append(q)

        self.length = len(components)
        self.components = components
        super().__init__(source, target)

    def reduce(self, mor: Mor):
        t = self.target
        assert isinstance(t, Product)

        q = t.q().reduce(mor)
        if q is None:
            return None

        p = t.p().reduce(mor)
        if p is None:
            return None

        return Pairing(Span(p, q, t.par))

    def __hash__(self):
        return hash(tuple(zip(self.components, range(self.length))))

    # @property
    # def par(self):
    #     t = self.target
    #     assert isinstance(t, Product)
    #     return t.par
