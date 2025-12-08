"""High level interface to category ambient"""
from collections.abc import Callable, Iterator, Sequence
from abc import ABCMeta, abstractmethod
from typing import Any, Self, TypeGuard, TypeVar, overload, NoReturn
from itertools import chain
from operator import attrgetter

from .cells import Obj, Mor, Eq
from .cells.category import Composition
from . import cells
from .public import category as public

Transformation = Callable[[Obj], Mor]
MorLike = Mor | Obj | Transformation
EqLike = MorLike | Eq

def _fit_mor(source: Obj, target: Obj, cell: Mor):
    # Subclasses of `Obj` can support specific type conversions. Handling of
    # transformations occurs before this (in which case no fitting is
    # needed).
    sconv = source.conversion(cell.source)
    if not sconv:
        raise cells.SourceUnfit("Can't convert", source, cell.source)

    tconv = cell.target.conversion(target)
    if not tconv:
        raise cells.TargetUnfit("Can't convert", cell.target, target)

    # This will be just `cell` when `tconv` as `sconv` are identities.
    return tconv.compose(cell).compose(sconv)

def _mor_like_to_mor(source: Obj, cell: MorLike):
    if isinstance(cell, Callable):
        return cell(source)

    if isinstance(cell, Obj):
        return cell.identity()

    return cell

def _source_fit_mor_like(source: Obj, cell: MorLike):
    cell = _mor_like_to_mor(source, cell)

    sconv = source.conversion(cell.source)
    if not sconv:
        raise cells.SourceUnfit(
            "Can't convert for fitting source", source, cell.source,
        )

    return cell.compose(sconv)

def _source_fit_eq(source: Obj, cell: Eq):
    sconv = source.conversion(cell.ssource.source)
    if not sconv:
        raise cells.SourceUnfit(
            "Can't convert for fitting source", source, cell.ssource.source,
        )

    return cell.compose_eq(sconv.ref())

def _ssource_fit_eq(ssource: Mor, cell: Eq):
    cell = _source_fit_eq(ssource.source, cell)

    sconv = ssource.conversion(cell.ssource)
    if not sconv:
        raise cells.SSourceUnfit(
            "Can't convert for fitting setoid source", ssource, cell.ssource,
        )

    return cell.trans(sconv)

def _fit_eq(ssource: 'Mor', starget: 'Mor', cell: Eq):
    prev_err = None
    for i in range(2):
        try:
            sconv = ssource.conversion(cell.ssource)
            if not sconv:
                raise cells.SSourceUnfit("Can't convert", ssource, cell.ssource)

            tconv = cell.starget.conversion(starget)
            if not tconv:
                raise cells.STargetUnfit("Can't convert", cell.starget, starget)
        except cells.MorUnfit as err:
            if i == 0:
                cell = cell.sym()
                prev_err = err
                continue

            raise err from prev_err

        return tconv.trans(cell).trans(sconv)

    assert False

def one[T](*args: T | None) -> T:
    """Returns the unique argument that is not None"""
    res: T | None = None
    for a in args:
        if a is not None:
            if res is None:
                res = a
            elif res is not a:
                if isinstance(res, Theory) and isinstance(a, type(res)):
                    res = res.with_base(a)
                else:
                    raise ValueError("More than one value was provided.")

    if res is None:
        raise ValueError("No value was provided.")

    return res

class Theory(metaclass=ABCMeta):
    """Base class for theories"""

    @abstractmethod
    def with_base(self, base: Any) -> Self:
        """Combine `self` and `base`"""

    @abstractmethod
    @classmethod
    def from_prim(cls, ctx: 'Context', prim: Any) -> Self:
        """Create theory from primitives"""
        # Some rules must be followed in the implementation, which are not
        # enforced through code. Attributes of `prim` must be used exactly once
        # to define variables of the same name. These variables must then be
        # used instead of accessing the attributes.
        # TODO: primitives can't be changed through conversion
        #       (including Obj -> Mor thorugh identity, etc.)!
        # TODO: primitives shouldn't be used (e.g. in composition, identity, etc.)
        #       before being named.

class Context:
    """Handles cells of a theory with ambient category"""
    __slots__ = ('name_stack',)
    name_stack: tuple[str, ...]

    compose = staticmethod(public.compose)
    compose_eq = staticmethod(public.compose_eq)
    trans = staticmethod(public.trans)
    sym = staticmethod(public.sym)
    identity = staticmethod(public.identity)
    ref = staticmethod(public.ref)
    #from wlex.ambient.public import category # TODO: This should be variable!
    # Have a Category class with all the backend functions, etc.?
    # ABC interface would be overkill, just use a dataclass with Callable attributes, etc.
    # The objects of category are Obj, Mor, Eq, which would be essentially hardcoded.
    # This isn't a problem as long as the accept method of backend.Obj is
    # isinstance(x, Obj), etc. Include only the actually publicly used cells of category.
    # The problem of using dataclass is that one ends up having to repeat all the function signatures.

    def __init__(self):
        self.name_stack = ()

    def with_name(self, name: str):
        """Copy of `self` with name added to its `name_stack`"""
        ctx = Context()
        ctx.name_stack = (*self.name_stack, name)
        return ctx

    def sub[T: Theory](
        self, name: str, theory: type[T], prim: T | None,
        base: T | None = None,
    ):
        """Sets name on subtheory"""
        if not prim:
            raise ValueError(f"Missing primitives for {theory.__name__}")

        if base:
            prim = prim.with_base(base)

        # There is checking for keeping attributes of `prim` from remaining
        # unused. Also, checking that the resulting theory has no empty
        # attributes.
        return theory.from_prim(self.with_name(name), prim)

    def _set_name(self, name: str, cell: cells.Cell):
        if not hasattr(cell, 'name'):
            cell.name = (*self.name_stack, name)

    def obj(self, name: str, cell: Obj | None):
        """Sets name on object"""
        if not cell:
            raise ValueError(f'Missing cell "{name}"')

        self._set_name(name, cell)
        return cell

    @overload
    def mor(
        self, name: str, cell: MorLike | None,
        signature: tuple[Obj, Obj] | None,
    ) -> Mor: ...
    @overload
    def mor(
        self, name: str, cell: MorLike | None,
        signature: tuple[Obj, Mor],
    ) -> tuple[Mor, Callable[[EqLike | None], Eq]]: ...
    @overload
    def mor(
        self, name: str, cell: MorLike | None,
        signature: tuple[Mor, Obj],
    ) -> tuple[Mor, Callable[[EqLike | None], Eq]]: ...
    @overload
    def mor(
        self, name: str, cell: MorLike | None,
        signature: tuple[Mor, Mor],
    ) -> tuple[Mor, Callable[[EqLike | None], Eq]]: ...

    def mor(
        self, name: str, cell: MorLike | None,
        signature: tuple[Obj | Mor, Obj | Mor] | None = None,
    ):
        """Sets name on morphism and checks signature"""
        # TODO: Check that there is no assumption about Transformation and Law preserving the (s)source.
        if not cell:
            raise ValueError(f'Missing cell "{name}"')

        if isinstance(cell, Obj):
            cell = cell.identity()

        if not signature:
            # Here `cell` can't be a transformation. A composition with
            # transformations can only be checked after providing a source.
            # For this and other reasons, it makes sense to not make
            # transformation part of the theory the way morphisms are.
            if isinstance(cell, Callable):
                raise TypeError(
                    "If `cell` is transformation, signature is needed.",
                )

            self._set_name(name, cell)
            return cell

        source, target = signature
        if isinstance(source, Obj):
            if isinstance(cell, Callable):
                # There is no assumption about source being preserved here.
                cell = cell(source)

            if isinstance(target, Obj):
                cell = _fit_mor(source, target, cell)
                self._set_name(name, cell)
                return cell

            return self._hat_mor(
                name, cell, (source, target.source),
                (source.identity(), target),
            )

        if isinstance(target, Obj):
            # Object `target` is disallowed here, because it would have the same
            # effect as setting the value of the morphism being created to
            # `source`. There must preferably be only one way to do things.
            raise TypeError(
                "If `source` is morphism, then so must be `target`.",
            )

        if isinstance(cell, Callable):
            cell = cell(source.source)

        return self._hat_mor(
            name, cell, (source.source, target.source), (source, target),
        )

    def _hat_mor(
        self, name: str, cell: Mor,
        signature: tuple[Obj, Obj], hat_signature: tuple[Mor, Mor],
    ) -> tuple[Mor, Callable[[EqLike | None], Eq]]:
        """Sets name on morphism and checks signature"""
        source, target = signature
        cell = _fit_mor(source, target, cell)
        hat_source, hat_target = hat_signature

        def _hat(c: EqLike | None):
            # We defer assigning hat, because we may end up needing cell in its
            # definition.
            return self.eq(
                f'^{name}', c, (hat_source, hat_target.compose(cell)),
            )

        self._set_name(name, cell)
        return cell, _hat

    def eq(
        self, name: str, cell: EqLike | None,
        ssignature: tuple[MorLike, MorLike] | None = None,
    ):
        """Sets name on equality and checks signature"""
        # There is no point in providing a `signature` besides the `ssignature`.
        # Is `ssource` and `starget` have to be made to fit, then `cell` must
        # also be modified. However, `cell.ssource` and `cell.starget` are
        # already aligned, and making `ssource` and `starget` be aligned would
        # be the main purpose of `signature`. One would be more interested in
        # making `ssource` match `cell.ssource` and `starget` match
        # `cell.starget`. Inferring composition (besides transitivity) for
        # accomplishing this is overkill.
        if not cell:
            raise ValueError(f'Missing cell "{name}"')

        if isinstance(cell, Obj):
            cell = cell.identity()

        if isinstance(cell, Mor):
            cell = cell.ref()

        if not ssignature:
            if isinstance(cell, Callable):
                raise TypeError(
                    "If `cell` is transformation, setoid signature is needed.",
                )

            self._set_name(name, cell)
            return cell

        ssource, starget = ssignature

        ssource, starget = (
            m.identity() if isinstance(m, Obj) else m
            for m in (ssource, starget)
        )

        if isinstance(ssource, Mor):
            if not isinstance(starget, Mor):
                starget = starget(ssource.source)
        elif isinstance(starget, Mor):
            ssource = ssource(starget.source)
        else:
            raise TypeError(
                "At least one of `ssource` and `starget` must be a morphism.",
            )

        if isinstance(cell, Callable):
            # There is no assumption about ssource being preserved here.
            cell = cell(ssource.source).ref()

        cell = _fit_eq(ssource, starget, cell)
        self._set_name(name, cell)
        return cell

ComposableT = TypeVar('ComposableT')
Composer = Callable[[tuple[ComposableT, ComposableT]], ComposableT]

def reduce[T](comp: Composer[T], factors: Iterator[T]) -> T:
    """Variadic composition"""
    acc: T | None = None
    for f in factors:
        acc = f
        break
    else:
        assert False

    for f in factors:
        acc = comp((f, acc))

    return acc

def gen_fit_mors(
    source: Obj, factors: Iterator[MorLike], next_source: Callable[[Mor], Obj],
):
    """Adapt the sources of morphisms"""
    for f in factors:
        f = _source_fit_mor_like(source, f)
        source = next_source(f)
        yield f

def gen_fit_eqs(
    source: Obj, factors: Iterator[EqLike], next_source: Callable[[Mor], Obj],
):
    """Adapt the sources of equalities"""
    for f in factors:
        if isinstance(f, Eq):
            f = _source_fit_eq(source, f)
            source = next_source(f.ssource)
            yield f
        else:
            f = _source_fit_mor_like(source, f)
            source = next_source(f)
            yield f.ref()

def _gen_fit_eqs_for_trans(ssource: Mor, factors: Iterator[EqLike]):
    # Conversion is done adapting the source and target from right to left.
    for f in factors:
        if isinstance(f, Eq):
            f = _ssource_fit_eq(ssource, f)
            ssource = f.starget
            yield f
        else:
            source = ssource.source
            f = _fit_mor(source, ssource.target, _mor_like_to_mor(source, f))
            ssource = f
            yield f.ref()

def _mor_compose(comp: Composer[Mor], factors: Iterator[Mor]):
    args = list(factors)
    # Discard LazyComposition, it is just for type checking.
    res = reduce(comp, iter(args))
    if res.depth > 5:
        return Composition.simplified(*list(reversed(args)))
    return res.expanded()

def _all_eq_like(
    factors: Sequence[EqLike | None],
) -> TypeGuard[Sequence[EqLike]]:
    return all(factors)

def _all_eq(
    factors: Sequence[EqLike | None],
) -> TypeGuard[Sequence[Eq]]:
    return all(isinstance(f, Eq) for f in factors)

def _all_mor_like(
    factors: Sequence[EqLike | None],
) -> TypeGuard[Sequence[MorLike]]:
    return all(f and not isinstance(f, Eq) for f in factors)

_get_target = attrgetter('target')

def _compose(
    comp: Composer[Mor],
    first: MorLike,
    factors: Sequence[MorLike]
) -> Mor | Transformation:
    factor_it = chain(reversed(factors), (first,))

    if factors:
        last = factors[-1]
    else:
        last = first

    if isinstance(last, Callable):
        def _comp(source: Obj):
            # This allows having more than one transformation in
            # factors.
            return _mor_compose(
                comp, gen_fit_mors(source, factor_it, _get_target),
            )

        return _comp

    if isinstance(last, Obj):
        source = last
    else:
        source = last.source

    return _mor_compose(comp, gen_fit_mors(source, factor_it, _get_target))

def _compose_eq(
    comp: Composer[Eq],
    first: EqLike,
    factors: Sequence[EqLike],
) -> Eq:
    if factors:
        last = factors[-1]
    else:
        last = first

    if isinstance(last, Callable):
        # The result here would be a callable, which is not a transformation, so
        # that it would only admit an explicit argument.
        raise TypeError(
            "Transformation is not allowed as the last factor of a composition "
            "containing equalities."
        )

    if isinstance(last, Obj):
        source = last
    elif isinstance(last, Mor):
        source = last.source
    else:
        source = last.ssource.source

    factor_it = chain(reversed(factors), (first,))
    return reduce(comp, gen_fit_eqs(source, factor_it, _get_target))

def operate_mor_or_eq(
    op_mor: Callable[[MorLike, Sequence[MorLike]], Mor | Transformation],
    op_eq: Callable[[EqLike, Sequence[EqLike]], Eq],
    first: EqLike | None, factors: Sequence[EqLike | None],
):
    """Handles variadic operation for morphisms and equalities"""
    if isinstance(first, Eq):
        assert _all_eq_like(factors)
        return op_eq(first, factors)

    if first:
        if _all_eq(factors):
            return op_eq(first, factors)

        assert _all_mor_like(factors)
        return op_mor(first, factors)

    raise ValueError("Missing factor")

def composer(ctx: Context):
    """Create function for variadic high-level composition"""
    comp = ctx.compose
    comp_eq = ctx.compose_eq

    def op_mor(
        first: MorLike, factors: Sequence[MorLike],
    ) -> Mor | Transformation:
        return _compose(comp, first, factors)

    def op_eq(
        first: EqLike, factors: Sequence[EqLike],
    ) -> Eq:
        return _compose_eq(comp_eq, first, factors)

    @overload
    def compose(first: MorLike | None, *factors: MorLike | None) -> Mor | Transformation: ...
    @overload
    def compose(first: Eq, *factors: EqLike | None) -> Eq: ...
    @overload
    def compose(first: MorLike, *factors: Eq) -> Eq: ...
    @overload
    def compose(first: None, *factors: EqLike | None) -> NoReturn: ...

    def compose(
        first: EqLike | None, *factors: EqLike | None,
    ) -> Mor | Transformation | Eq:
        return operate_mor_or_eq(op_mor, op_eq, first, factors)

    return compose

# TODO: How does one handle defensive args? It seems `compose` would have to
# be wrapped inside a function that accepts type object instead of MorLike, etc.
# and then does dynamic type-checking. This dynamic type-checking would obviously
# be part of the internalization (using a theory as backend).
# This would require a separate `composer`, which seems to kill the point of having
# typed comp and comp_eq args!
# The way to go is too keep all the type annotations and wrap dynamically type-checked
# functions. For defensive type checking one also relies on wrapping the non-annotated
# functions and initialized the Defensive argument in the wrapper. It may be the case
# however that a non-annotated callable can be used as Composer[T].
# Should one directly instantiate Composition instead of leaving as LazyComposition?
# Variadic compose being outside the theory doesn't have a way to handle type checking
# beyond the binary compose functions that underlie it.

def _trans(trans_: Composer[Eq], first: EqLike, factors: Sequence[EqLike]) -> Eq:
    if factors:
        last = factors[-1]
    else:
        last = first

    if isinstance(last, Callable):
        raise TypeError(
            "Transformation is not allowed as last factor when applying "
            "transitivity."
        )

    if isinstance(last, Obj):
        ssource = last.identity()
    elif isinstance(last, Mor):
        ssource = last
    else:
        ssource = last.ssource

    factor_it = chain(reversed(factors), (first,))
    return reduce(trans_, _gen_fit_eqs_for_trans(ssource, factor_it))

def transitivity(ctx: Context):
    """Creates function for variadic high-level composition"""
    trans_ = ctx.trans

    def trans(first: EqLike | None, *factors: EqLike | None):
        if first and _all_eq_like(factors):
            return _trans(trans_, first, factors)

        raise ValueError("Missing factor")

    return trans
