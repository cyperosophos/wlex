"""Cart cell classes"""
from typing import Self, TypeGuard, override, Union
from collections.abc import Sequence, MutableSequence, Generator, Mapping
from abc import ABCMeta

from ..cells import Obj, Mor, Eq, PrimMor
from .category import (
    CategoryObj, CategoryMor, CategoryEq, CategoryPrimEq, Composition,
)

class CartObj(CategoryObj, metaclass=ABCMeta):
    """Models object `cart.Obj`"""
    __slots__ = ()

    _product_cls: type['Product']
    _product_mor_cls: type['ProductMor']

    @classmethod
    def init_cls(cls):
        cls._composition_cls = CartComposition
        cls._product_cls = Product
        cls._product_mor_cls = ProductMor

    @override
    @classmethod
    def terminal(cls):
        return cls.vproduct(())

    @override
    def terminal_mor(self):
        return self.vproduct_mor(())

    @override
    def product(self, y: Obj):
        x = self
        return self.vproduct((('x', x), ('y', y)))

    @override
    @classmethod
    def vproduct(
        cls,
        params: Sequence[tuple[str, Obj]],
        no_repeat: bool = False,
    ):
        return cls._product_cls(params, no_repeat=no_repeat)

    @override
    def vproduct_mor(
        self,
        params: Sequence[tuple[str, Mor]],
    ) -> Mor:
        return self._product_mor_cls(self, params)

class CartMor(CategoryMor, metaclass=ABCMeta):
    """Models object `cart.Mor`"""
    __slots__ = ()

    @override
    def same(self, x: Mor):
        # We handle sameness of terminal morphisms here.
        terminal = self.source.terminal()
        return super().same(x) or (
            self.target.identical(terminal)
            and x.target.identical(terminal)
            and self.source.identical(x.source)
        )

    @override
    def pairing(self, q: Mor):
        p = self
        return p.source.vproduct_mor((('p', p), ('q', q)))

    @override
    def pairing_unique(self, p: Mor, q: Mor):
        mor = self
        eq = Eq(p.pairing(q), mor)
        eq.proven = True
        return eq

class CartPrimMor(PrimMor, CartMor, metaclass=ABCMeta):
    """Models object `cart.Mor` as primitive"""
    __slots__ = ()

CartEq = CategoryEq
CartPrimEq = CategoryPrimEq

class ComponentMap[T](Mapping[str | int, T]):
    __slots__ = '_map', '_values', '_keys'

    _map: dict[str | int, T] | None
    _data: frozenset[tuple[str | int, T]] | None
    _values: tuple[T, ...] | None

    def __init__(self, data: Sequence[tuple[str | int, T]]):
        if all(i == l for i, (l, _) in enumerate(data)):
            self._map = None
            self._data = None
            self._values = tuple(c for (_, c) in data)
        else:
            self._map = dict((k, v) for k, v in data if k != '')
            self._keys = frozenset(data)
            self._values = None

    def __init__2(self, values: tuple[T, ...] | dict[str | int, T], keys: tuple[str, ...] | None = None):
        if keys is None:
            if isinstance(values, tuple):
                self._map = None
                self._keys = None
                self._values = values
            else:
                self._map = values
                self._keys = tuple(sorted(values))
                self._values = tuple(values[l] for l in self._keys)
        else:
            assert isinstance(values, tuple)
            self._map = dict((k, v) for k, v in zip(keys, values) if k)
            self._keys = tuple(sorted(keys))
            self._values = tuple(self._map[l] for l in self._keys)

    #def as_dict_or_tuple(self):
    #    if self._map is None:
    #        return self._values

    #    return self._map

    def __getitem__(self, key: str | int):
        if self._map is None:
            if isinstance(key, int):
                return self._values[key]

            raise KeyError

        if isinstance(key, str):
            return self._map[key]

        raise KeyError

    def __iter__(self):
        if self._map is None:
            return iter(range(len(self._values)))

        return iter(self._map)

    def __len__(self):
        return len(self._values)

    def __hash__(self):
        return hash((self._keys, self._values))

class Product(CartObj):
    """Models object corresponding to source of span `cart.product`"""
    __slots__ = ('components',)

    components: ComponentMap[Obj]

    def trim(self, obj: Obj):
        # Includes weakening
        res = super().trim(obj)
        if res is not None:
            return res

        if not isinstance(obj, Product):
            return None

        comps = self.components.as_dict_or_tuple()
        ocomps = obj.components.as_dict_or_tuple()

        if isinstance(comps, tuple):
            if not isinstance(ocomps, tuple):
                return None

            # No weakening
            if len(comps) != len(ocomps):
                return None

            convs: list[Mor] = []
            for c, oc in zip(comps, ocomps):
                conv = c.conversion(oc)
                if conv is None:
                    return None

                convs.append(conv)

            return self.vproduct_mor(tuple(
                c.compose(obj.proj(i))
                for i, c in enumerate(convs)
            ))

        # ...
        components = self.components
        labeled_convs: list[tuple[str, Mor]] = []
        for label, c in obj.components.items():
            if label not in components:
                return None

            conv = c.trim(components[label])
            if conv is None:
                return None

            labeled_convs.append((label, conv))

        return self.vproduct_mor([
            (label, c.compose(obj.proj(label)))
            for label, c in labeled_convs
        ])

    @override
    def proj(self, label: str | int):
        return Projection.from_path(self, (label,))

    def __new__(cls, components: ComponentMap[Obj] | tuple[Obj]):
        if not components:
            terminal = getattr(cls, '_terminal', None)
            if isinstance(terminal, cls):
                return terminal

            cls._terminal = super().__new__(cls)

        return super().__new__(cls)

    @staticmethod
    def _add_component(agg: dict[str, Obj], label: str, component: Obj, no_repeat: bool):
        if label in agg:
            if no_repeat:
                raise ValueError("No repeats allowed")

            if not component.identical(agg[label]):
                raise ValueError("Types with same label must be identical.")
        else:
            agg[label] = component

    @classmethod
    def make_components(cls, params: Sequence[tuple[str, Obj]], no_repeat: bool = False):
        if len(params) == 1:
            l, c = params[0]
            if not l and isinstance(c, Product):
                raise ValueError(
                    "Can't have single product as component, since this just "
                    "creates a copy of the product",
                )

        agg: dict[str, Obj] = {}
        for label, component in params:
            if label:
                cls._add_component(agg, label, component, no_repeat)
            else:
                if not isinstance(component, Product):
                    raise ValueError("Unlabeled component must be product.")

                comps = component.components.as_dict_or_tuple()
                if isinstance(comps, tuple):
                    raise ValueError("Product component must have labels.")

                for l, c in comps.items():
                    cls._add_component(agg, l, c, no_repeat)

        return ComponentMap(agg)

    @classmethod
    def from_labeled_objects(cls,  params: Sequence[tuple[str, Obj]], no_repeat: bool = False):
        return cls(cls.make_components(
            params, no_repeat=no_repeat,
        ))

    def __init__(
        self,
        components: ComponentMap[Obj] | tuple[Obj],
    ):
        # Repeated component labels are allowed. This is based on the fact that
        # AxBxC is the pullback of the projections AxB->B and BxC->B.

        # Avoid reinitializing terminal object
        if (
            not components and self is self._terminal
            and hasattr(self, 'components')
        ):
            return

        if isinstance(components, ComponentMap):
            self.components = components
        else:
            self.components = ComponentMap(components)

    def identical(self, x: Obj):
        return super().identical(x) or (
            isinstance(x, Product)
            and len(self.components) == len(x.components)
            and all(
                l in x.components and c.identical(x.components[l])
                for l, c in self.components.items()
            )
        )

    def hint(self):
        return self.components

    def accepts(self, x: object):
        # No type accepts None!
        return (
            (_isinstance_dict_str_object(x) or _isinstance_tuple_object(x))
            and len(self.components) != len(x)
            and all(
                l in x and c.accepts(_gi(x, l))
                for l, c in self.components.items()
            )
        )

    def same(self, x: object, y: object):
        return (
            (
                (_isinstance_dict_str_object(x) and _isinstance_dict_str_object(y))
                or (_isinstance_tuple_object(x) and _isinstance_tuple_object(y))
            )
            and len(x) == len(y)
            and all(
                l in x and l in y and c.same(_gi(x, l), _gi(y, l))
                for l, c in self.components.items()
            )
        )

def _isinstance_tuple_object(x: object) -> TypeGuard[tuple[object]]:
    return isinstance(x, tuple)

def _isinstance_dict_str_object(x: object) -> TypeGuard[dict[str, object]]:
    return (
        isinstance(x, dict)
        and all(isinstance(k, str) for k in x) # pyright: ignore[reportUnknownVariableType]
    )

def _is_identity(mor: Mor):
    # Identity in an extensional sense
    return isinstance(mor, Composition) and mor.factors == ()

def _gi(x: tuple[object] | dict[str, object], key: str | int):
    if isinstance(x, tuple):
        if isinstance(key, str):
            return None

        if key >= len(x):
            return None

        return x[key]

    if isinstance(key, int):
        return None

    return x.get(key)

class Projection(CartMor):
    "Models morphism corresponding to projection"
    __slots__ = ('path',)
    path: tuple[str | int, ...]

    def __init__(
        self, source: Product, target: Obj, path: tuple[str | int, ...],
    ):
        self.path = path # polish order
        super().__init__(source, target)

    @classmethod
    def from_path(cls, source: Product, path: Sequence[str | int]):
        """Create projection from path"""
        target = source

        if len(path) < 1:
            raise ValueError("`path` can't be empty.")

        for label in path:
            if isinstance(target, Product):
                target = target.components[label]
            else:
                raise ValueError("`source` not deep enough for `path`")

        return cls(source, target, tuple(path))

    def proj_compose(self, mor: Self):
        """Compose with projections into a single projection"""
        source = mor.source
        target = self.target
        assert isinstance(source, Product)

        return Projection(source, target, (*mor.path, *self.path))

    def ev(self, x: object):
        for label in self.path:
            x = _gi(x, label) # pyright: ignore[reportArgumentType]

        assert isinstance(x, object)
        return x

    def same(self, x: Mor):
        return super().same(x) or (
            isinstance(x, Projection)
            and self.path == x.path
            and self.source.identical(x.source)
        )

    def hint(self):
        return self.path, self.source

class ProductMor(CartMor):
    """Models object corresponding to `cart.ProductMor`"""
    __slots__ = 'components', '_inplace'

    #components: frozenset[tuple[str, Mor]]
    #_labeled_components: dict[str, Mor]
    components: ComponentMap[Mor]
    _inplace: bool

    def get_component(self, label: str | int):
        return self.components.get(label)

    def after_proj(self, mor: Projection) -> Mor | tuple[Mor, Mor]:
        """Get the morphism associated to projection in the pairing

        The composition of `self` and `mor` may sometimes not reduce to a single
        morphism. This is the case when the target of the resulting morphism
        does not coincide with the target of the projection. When this occurs, a
        tuple of two morphisms is returned, the first one being the adapted
        projection and the second one being the resulting morphism.
        """
        res = self

        # Empty `path` is not allowed, since it would make Projection an
        # identity.
        for i, label in enumerate(mor.path):
            if isinstance(res, ProductMor):
                component = res.get_component(label)
                if component is not None:
                    res = component
                    continue

            # The returned projection is truncated to include all remaining
            # indices with the target of `res` as its source.
            t = res.target
            assert isinstance(t, Product)
            return Projection.from_path(t, mor.path[i:]), res

        return res

    def component_compose(self, mor: Mor):
        """Compose each component with `mor`"""
        for label, component in self.components:
            yield label, component.compose(mor)

    @classmethod
    def make_target_components(cls, params: Sequence[tuple[str, Mor]]):
        return Product.make_components([
            (label, component.target)
            for label, component in params
        ], no_repeat=True)

    @classmethod
    def make_components(cls, params: Sequence[tuple[str, Mor]]):
        mors: list[tuple[str, Mor]] = []
        for label, component in params:
            if label or not isinstance(component, ProductMor):
                mors.append((label, component))
            else:
                comps = component.components.as_dict_or_tuple()
                if isinstance(comps, tuple):
                    raise ValueError("ProductMor component must have labels.")

                mors.extend(comps.items())

        return ComponentMap(tuple(mors))


    def __init__(
        self, source: Obj,
        components: ComponentMap[Mor] | tuple[Mor],
    ):
        if isinstance(components, ComponentMap):
            self.components = components
            target = Product.from_labeled_objects([
                (l, c.target) for l, c in components.items()
            ], no_repeat=True)
        else:
            self.components = ComponentMap(components)


        self._inplace = False
        self._labeled_components = {}

        for label, component in components:
            if label:
                target = component.target
                target_components.append((label, target))
                mors.append((label, component))
                self._labeled_components[label] = component
            else:
                target = component.target
                if not isinstance(target, Product):
                    raise ValueError(
                        "Morphism without label just have product as target.",
                    )

                target_components.append(('', target))
                if isinstance(component, ProductMor):
                    # Flatten. Notice that target will be at least as flat as
                    # morphism.
                    mors.extend(component.components)
                else:
                    if _is_identity(component): # This misses identity in ProductMor component!
                        self._inplace = True

                    mors.append(('', component))

        target = source.vproduct(target_components, no_repeat=True)
        self.components = frozenset(mors) # No overlaps!
        super().__init__(source, target)

    def same(self, x: Mor):
        return super().same(x) or (
            isinstance(x, ProductMor)
            and len(self.components) == len(x.components)
            and all(lmor in x.components for lmor in self.components)
        )

    def hint(self):
        return self.components

    def ev(self, x: object):
        components = self.components
        if self._inplace:
            assert _isinstance_dict_str_object(x)
            for label, component in components:
                if label:
                    x[label] = component.ev(x)
                else:
                    if _is_identity(component):
                        continue

                    y = component.ev(x)
                    assert _isinstance_dict_str_object(y)
                    for k, v in y.items():
                        x[k] = v

            return x

        res: dict[str, object] = {}
        for label, component in components:
            if label:
                res[label] = component.ev(x)
            else:
                y = component.ev(x)
                assert _isinstance_dict_str_object(y)
                for k, v in y.items():
                    res[k] = v

        return res

# TODO: Review this!
class CartComposition(Composition, CartMor):
    """Handles extra conditions that make two morphisms the same

    The extra condition is the one coming from composition of pairing and
    projection.
    """
    __slots__ = ()

    @classmethod
    def _simplify_proj(cls, pmor: Mor, mor: Mor) -> Mor | tuple[Mor, Mor]:
        # `pmor` is a morphism with projections such as (f @ a$, g @ b$). When
        # composing with (a=m, b=n), one normalizes to (f @ m, g @ n).
        # Composing with a morphism that is not (extensionally) a pairing
        # cannot lead to normalization, because then the morphism would have to
        # be duplicated. Something like the naturality of the diagonal would
        # still be intensional. Normalization (simplification) gets applied
        # left-associatively. There is no backtracking. Duplication of
        # projections and identities is allowed. This includes composition and
        # pairing of projections, which are actually projections of products of
        # products.

        # First step is to compose with each component of `pmor`. Next step is
        # to simplify each resulting component. Since simplification is applied
        # left-associatively, one only takes the last two factors into account.

        if isinstance(pmor, Composition):
            if pmor.factors:
                # This assumes tail will never be an identity.
                tail, head = pmor.split()
                mm = cls._simplify_proj(head, mor)

                if isinstance(mm, tuple):
                    p, m = mm
                    return tail.compose(p), m

                return tail, mm

            return mor

        return cls._simplify_proj_single_factor(pmor, mor)

    @classmethod
    def _simplify_proj_single_factor(
        cls, pmor: Mor, mor: Mor,
    ) -> Mor | tuple[Mor, Mor]:
        if isinstance(pmor, Projection):
            if isinstance(mor, Projection):
                return pmor.proj_compose(mor)

            if isinstance(mor, ProductMor):
                return mor.after_proj(pmor)

            return pmor, mor

        if isinstance(pmor, ProductMor):
            expensive: set[Mor] = set()
            params: list[tuple[str, Mor]] = []
            for label, m in pmor.component_compose(mor):
                # If there is a repeated "expensive" morphism, then don't
                # simplify. An "expensive" morphism is one that is not a
                # projection nor a pairing of projections.
                if not cls._extract_expensive_no_repeat(m, expensive):
                    return pmor, mor

                params.append((label, m))

            return mor.source.vproduct_mor(params)

        return pmor, mor

    @classmethod
    def _extract_expensive_no_repeat(cls, mor: Mor, dst: set[Mor]) -> bool:
        # As stated above terminal morphisms get excluded from components.
        if isinstance(mor, Projection):
            return True

        if isinstance(mor, ProductMor):
            return all(
                cls._extract_expensive_no_repeat(m, dst)
                for _, m in mor.components
            )

        if mor in dst:
            return False

        dst.add(mor)
        return True

    @classmethod
    def simplify(cls, factors: Sequence[Mor]):
        factor_it = iter(super().simplify(factors))
        for prev in factor_it:
            break
        else:
            return ()

        _factors: list[Mor] = []
        for factor in factor_it:
            # The resulting morphism (or first morphism) will have the same
            # target as `prev`.
            mm = cls._simplify_proj(prev, factor)
            if isinstance(mm, tuple):
                p, prev = mm
                _factors.append(p)
            else:
                prev = mm
        _factors.append(prev)

        return _factors

CartObj.init_cls()
