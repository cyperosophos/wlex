"""Cart cell classes"""
from typing import Self, TypeGuard, override
from collections import defaultdict
from collections.abc import Sequence, Mapping, Iterator
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
        params: Sequence[tuple[str | int, Obj]],
        no_repeat: bool = False,
    ):
        return cls._product_cls(params, no_repeat=no_repeat)

    @override
    def vproduct_mor(
        self,
        params: Sequence[tuple[str | int, Mor]],
    ):
        # Handle case of unlabeled morphism with product target.
        if len(params) == 1:
            l, c = params[0]
            if not l and isinstance(c.target, Product):
                return c

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
    __slots__ = '_map', 'data', 'tup'

    _map: dict[str | int, T] | None # Contains only values with non-empty labels
    data: frozenset[tuple[str | int, T]] | None
    tup: tuple[T, ...]

    def __init__(self, data: Sequence[tuple[str | int, T]]):
        if set(range(len(data))) == set(k for k, _ in data):
            self._map = None
            self.data = None
            self.tup = tuple(c for (_, c) in sorted(data))
        else:
            self._map = dict((k, v) for k, v in data if k != '')
            self.data = frozenset(data)
            self.tup = ()

    def __getitem__(self, key: str | int):
        if self._map is None:
            if isinstance(key, int):
                return self.tup[key]

            raise KeyError

        return self._map[key]

    def __iter__(self):
        if self._map is None:
            return iter(range(len(self.tup)))

        return iter(self._map)

    def __len__(self):
        if self._map is None:
            return len(self.tup)

        return len(self._map)

    def __hash__(self):
        return hash(self.data or self.tup)

    def full_eq(self, x: Self):
        if self._map is None:
            return self.tup == x.tup

        return self.data == x.data

    def full_items(self):
        if self.data is None:
            return enumerate(self.tup)

        return iter(self.data)

    def full_len(self):
        if self.data is None:
            return len(self.tup)

        return len(self.data)

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

        components = self.components
        conversions: list[tuple[str | int, Mor]] = []
        for label, c in obj.components.items():
            if label not in components:
                return None

            conv = c.trim(components[label])
            if conv is None:
                return None

            conversions.append((label, conv))

        return self.vproduct_mor([
            (label, c.compose(obj.proj(label)))
            for label, c in conversions
        ])

    @override
    def proj(self, label: str | int):
        return Projection.from_path(self, (label,))

    def __new__(cls, components: Sequence[tuple[str | int, Obj]], no_repeat: bool = False):
        if not components:
            terminal = getattr(cls, '_terminal', None)
            if isinstance(terminal, cls):
                return terminal

            cls._terminal = super().__new__(cls)

        if len(components) == 1:
            l, c = components[0]
            if not l and isinstance(c, Product):
                return c

        return super().__new__(cls)

    @staticmethod
    def _add_component(
        agg: dict[str | int, Obj],
        label: str | int,
        component: Obj,
        no_repeat: bool
    ):
        if label in agg:
            if no_repeat:
                raise ValueError("No repeats allowed")

            if not component.identical(agg[label]):
                raise ValueError("Types with same label must be identical.")
        else:
            agg[label] = component

    def with_labels(self, relabeling: dict[str | int, str | int] | Sequence[str | int]):
        # Order is preserved when there is no (de)flattening.
        def agg(rl: Iterator[tuple[str | int, str | int, Obj]]):
            m: dict[str | int, list[tuple[str | int, Obj]]] = defaultdict(list)
            for old, new, obj in rl:
                m[new].append((old, obj))

            res = [(
                label,
                objs[0][1] if len(objs) == 1
                else self.vproduct(objs, no_repeat=True),
            ) for label, objs in m.items() if label != '']

            if '' in m:
                res.extend(('', obj) for _, obj in m[''])

            return res

        # This allows flattening product components potentially introducing
        # overlaps (which we avoid by setting `no_repeat=True`). Otherwise,
        # this does not introduce overlaps, but instead aggregates all
        # repeated relabeling into a single product component.
        if isinstance(relabeling, dict):
            for label in relabeling:
                if label not in self.components:
                    raise ValueError("Can't relabel `{label}` in product")

            return self.vproduct(agg(
                (label, relabeling.get(label, label), component)
                for label, component in self.components.items()
            ), no_repeat=True)

        if len(relabeling) > len(self.components):
            raise ValueError("Product relabeling list is too long.")

        # This works because if the labels are a range of numbers (from 0), then
        # they will be ordered when initializing components, so that labeling
        # based on the order of labels is the same as labeling based on their
        # values.
        return self.vproduct(agg(
            (label, relabeling[i], component)
            for i, (label, component) in enumerate(self.components.items())
        ), no_repeat=True)

    l = with_labels

    def relabel(self, relabeling: dict[str | int, str | int] | Sequence[str | int]):
        # TODO: Does this actually work? It seems too easy.
        def agg(rl: Iterator[tuple[str | int, str | int, Mor]]):
            m: dict[str | int, list[tuple[str | int, Mor]]] = defaultdict(list)
            for old, new, mor in rl:
                m[new].append((old, mor))

            res = [(
                label,
                mors[0][1] if len(mors) == 1
                else self.vproduct_mor(mors),
            ) for label, mors in m.items() if label != '']

            if '' in m:
                res.extend(('', mor) for _, mor in m[''])

            return res

        # This should work with empty labels.
        if isinstance(relabeling, dict):
            for label in relabeling:
                if label not in self.components:
                    raise ValueError("Can't relabel `{label}` in product")

            return self.vproduct_mor(agg(
                (label, relabeling.get(label, label), self.proj(label))
                for label in self.components
            ))

        if len(relabeling) > len(self.components):
            raise ValueError("Product relabeling list is too long.")

        return self.vproduct_mor(agg(
            (label, relabeling[i], self.proj(label))
            for i, label in enumerate(self.components)
        ))

    def invert_relabeling(self, relabeling: dict[str | int, str | int] | Sequence[str | int]):
        res: dict[str | int, str | int] = {}

        if isinstance(relabeling, dict):
            it = relabeling.items()
        else:
            it = enumerate(relabeling)

        for k, v in it:
            if v == '':
                # The idea is that `self` can be considered as the product to be
                # relabeled with `relabeling`, so that the new product would end
                # up having the labels of the flattened component.
                c = self.components[k]
                if not isinstance(c, Product):
                    raise ValueError("Empty relabeling requires product component.")

                for l in c.components:
                    if l in res:
                        raise ValueError("Can't introduce overlap")

                    res[l] = k
            elif v in res:
                res[v] = ''
            else:
                res[v] = k

        return res

    def __init__(self, components: Sequence[tuple[str | int, Obj]], no_repeat: bool = False):
        # Repeated component labels are allowed. This is based on the fact that
        # AxBxC is the pullback of the projections AxB->B and BxC->B.

        # Avoid reinitializing terminal object
        if (
            not components and self is self._terminal
            and hasattr(self, 'components')
        ):
            return

        if len(components) == 1:
            l, c = components[0]
            if not l and isinstance(c, Product):
                return

        agg: dict[str | int, Obj] = {}
        for label, component in components:
            if label != '':
                self._add_component(agg, label, component, no_repeat)
            else:
                if not isinstance(component, Product):
                    raise ValueError("Unlabeled component must be product.")

                for l, c in component.components.items():
                    assert l != ''
                    self._add_component(agg, l, c, no_repeat)

        self.components = ComponentMap(list(agg.items()))
        assert len(self.components) == self.components.full_len()

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
            _is_product_acceptable(x)
            and len(self.components) != len(x)
            and all(
                l in x and c.accepts(_gi(x, l))
                for l, c in self.components.items()
            )
        )

    def same(self, x: object, y: object):
        return (
            _is_product_acceptable(x)
            and _is_product_acceptable(y)
            and len(x) == len(y)
            and all(
                l in x and l in y and c.same(_gi(x, l), _gi(y, l))
                for l, c in self.components.items()
            )
        )

def _insert_or_pad(dest: list[object], idx: int, v: object):
    while idx >= len(dest):
        dest.append(None)

    assert dest[idx] is None
    dest[idx] = v

def _isinstance_tuple_object(x: object) -> TypeGuard[tuple[object]]:
    return isinstance(x, tuple)

def _isinstance_dict_str_object(x: object) -> TypeGuard[dict[str | int, object]]:
    return (
        isinstance(x, dict)
        and all(isinstance(k, (str, int)) for k in x) # pyright: ignore[reportUnknownVariableType]
    )

def _is_product_acceptable(x: object) -> TypeGuard[tuple[object] | dict[object, object]]:
    return isinstance(x, (tuple, dict))

def _is_identity(mor: Mor):
    # Identity in an extensional sense
    return isinstance(mor, Composition) and mor.factors == ()

def _gi(x: tuple[object] | dict[object, object], key: str | int):
    if isinstance(x, tuple):
        if isinstance(key, str):
            return None

        if key >= len(x):
            return None

        return x[key]

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

# TODO: Does this work well with terminal morphisms?
class ProductMor(CartMor):
    """Models object corresponding to `cart.ProductMor`"""
    __slots__ = 'components', 'inplace'

    components: ComponentMap[Mor]
    inplace: bool

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
                component = res.components.get(label)
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
        for label, component in self.components.full_items():
            yield label, component.compose(mor)

    def idx_to_labels(self, relabeling: Sequence[str | int]):
        # if isinstance(relabeling, dict):
        #     for label in relabeling:
        #         if label not in self.components:
        #             raise ValueError("Can't relabel `{label}`")

        #     return self.source.vproduct_mor([
        #         (relabeling.get(label, label), component)
        #         for label, component in self.components.items()
        #     ])

        if len(relabeling) > len(self.components):
            raise ValueError("Relabeling list is too long.")

        return self.source.vproduct_mor([
            (relabeling[i], component)
            for i, component in enumerate(self.components.values())
        ])

    l = idx_to_labels

    def __new__(
        cls, source: Obj,
        components: Sequence[tuple[str | int, Mor]],
    ):
        if len(components) == 1:
            l, c = components[0]
            if not l:
                if isinstance(c, ProductMor):
                    return c

        return super().__new__(cls)

    def __init__(
        self, source: Obj,
        components: Sequence[tuple[str | int, Mor]],
    ):
        # Since this creates the target as a product this cannot be used
        # directly with morphisms with Subobject targets (e.g. EqualizerMor).
        if len(components) == 1:
            l, c = components[0]
            if not l:
                if isinstance(c, ProductMor):
                    return

                assert not isinstance(c.target, Product)

        target = source.vproduct([(l, c.target) for l, c in components], no_repeat=True)
        mors: list[tuple[str | int, Mor]] = []
        self.inplace = False
        for label, component in components:
            if label != '' or not isinstance(component, ProductMor):
                mors.append((label, component))
                if _is_identity(component):
                    self.inplace = True
            else:
                # Flatten. Notice that target will be at least as flat as
                # morphism.
                mors.extend(component.components.items())
                if component.inplace:
                    self.inplace = True

        self.components = ComponentMap(mors)
        super().__init__(source, target)

    def same(self, x: Mor):
        return super().same(x) or (
            isinstance(x, ProductMor)
            and self.components.full_eq(x.components)
        )

    def hint(self):
        return self.components

    def ev(self, x: object):
        def update(dest: dict[object, object], src: object):
            if _isinstance_dict_str_object(src):
                for k, v in src.items():
                    assert k not in res
                    dest[k] = v
            else:
                assert _isinstance_tuple_object(src)
                for k, v in enumerate(src):
                    assert k not in res
                    dest[k] = v

        components = self.components
        if (
            self.inplace
            and _is_product_acceptable(x)
            and isinstance(x, dict)
        ):
            for label, component in components.full_items():
                if label != '':
                    x[label] = component.ev(x)
                else:
                    if _is_identity(component):
                        continue

                    y = component.ev(x)
                    update(x, y)

            return x

        target = self.target
        assert isinstance(target, Product)
        if target.components.tup:
            dest: list[object] = []
            for label, component in components.full_items():
                if label != '':
                    assert isinstance(label, int)
                    _insert_or_pad(dest, label, component.ev(x))
                else:
                    y = component.ev(x)
                    if _isinstance_dict_str_object(y):
                        for k, v in y.items():
                            assert isinstance(k, int)
                            _insert_or_pad(dest, k, v)
                    else:
                        assert _isinstance_tuple_object(y)
                        for k, v in enumerate(y):
                            _insert_or_pad(dest, k, v)

        res: dict[object, object] = {}
        for label, component in components.full_items():
            if label != '':
                res[label] = component.ev(x)
            else:
                y = component.ev(x)
                update(res, y)

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
            params: list[tuple[str | int, Mor]] = []
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
                for _, m in mor.components.full_items()
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
