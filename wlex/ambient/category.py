"""High level interface to category ambient"""
from collections.abc import Callable, Iterator, Sequence
from abc import ABCMeta, abstractmethod
from typing import Any, Self, TypeGuard, TypeVar, overload
from itertools import chain

from .cells import Obj, Mor, Eq
from .cells.category import Composition
from . import cells
from .public import category as public

class CellFromObj[T: Mor | Eq]:
    """Base class of `Transformation` and `Law`"""
    __slots__ = ('_func',)

    def __init__(self, func: Callable[[Obj], T]):
        self._func = func

    def __call__(self, source: Obj):
        cell = self._func(source)

        if not hasattr(cell, 'name'):
            if hasattr(source, 'name'):
                cell.name = (*source.name, self.name)
            else:
                cell.name = (self.name,)

        return cell

    @property
    def name(self):
        """Name"""
        return self._func.__name__

class Transformation(CellFromObj[Mor]): # pylint: disable=R0903
    """Source dependent morphism"""

class Law(CellFromObj[Eq]): # pylint: disable=R0903
    """Source dependent equality"""

MorLike = Mor | Obj | Transformation
EqLike = MorLike | Eq | Law

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

def _source_fit_mor_like(source: Obj, cell: MorLike):
    if isinstance(cell, Transformation):
        cell = cell(source)

    if isinstance(cell, Obj):
        cell = cell.identity()

    sconv = source.conversion(cell.source)
    if not sconv:
        raise cells.SourceUnfit(
            "Can't convert for fitting source", source, cell.source,
        )

    return cell.compose(sconv)

def _source_fit_eq_or_law(source: Obj, cell: Eq | Law):
    if isinstance(cell, Law):
        cell = cell(source)

    sconv = source.conversion(cell.ssource.source)
    if not sconv:
        raise cells.SourceUnfit(
            "Can't convert for fitting source", source, cell.ssource.source,
        )

    return cell.compose_eq(sconv.ref())

def _ssource_fit_eq(ssource: Mor, cell: Eq):
    cell = _target_fit_eq(ssource.source, cell)

    sconv = ssource.conversion(cell.ssource)
    if not sconv:
        cell = cell.sym()
        sconv = ssource.conversion(cell.ssource)

        if not sconv:
            raise cells.SSourceUnfit(
                "Can't convert for fitting setoid source",
                ssource, cell.ssource,
            )

    return cell.trans(sconv)

def _target_fit_eq(target: Obj, cell: Eq):
    tconv = cell.ssource.target.conversion(target)
    if not tconv:
        raise cells.TargetUnfit(
            "Can't convert for fitting target", cell.ssource.target, target,
        )

    return tconv.ref().compose_eq(cell)

def _fit_eq(ssource: Mor, starget: Mor, cell: Eq):
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
                if isinstance(res, TheoryStub):
                    res = res.with_base(a)
                else:
                    raise ValueError("More than one value was provided.")

    if res is None:
        raise ValueError("No value was provided.")

    return res

class TheoryStub(metaclass=ABCMeta): # pylint: disable=R0903
    """Base class for the theory stub"""

    @abstractmethod
    def with_base(self, base: Any) -> Self:
        """Combine `self` and `base`"""

class Theory(metaclass=ABCMeta):
    """Base class for theories"""

    Stub: type[TheoryStub]

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

    @classmethod
    def is_own_stub(cls, stub: TheoryStub):
        """Stub corresponds to theory"""
        return isinstance(stub, cls.Stub)

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

    def sub[S: TheoryStub, T: Theory](
        self, name: str, theory: type[T], prim: S,
        base: S | None = None,
    ):
        """Sets name on subtheory"""
        # Pylance type checking does not catch this!
        if not theory.is_own_stub(prim):
            raise TypeError("Wrong stub class")

        if base:
            prim = prim.with_base(base)

        # There is checking for keeping attributes of `prim` from remaining
        # unused. Also, checking that the resulting theory has no empty
        # attributes.
        return theory.from_prim(self.with_name(name), prim)

    def _set_name(self, name: str, cell: cells.Cell):
        if not hasattr(cell, 'name'):
            cell.name = (*self.name_stack, name)

    def obj(self, name: str, cell: Obj):
        """Sets name on object"""
        self._set_name(name, cell)
        return cell

    @overload
    def mor(
        self, name: str, cell: MorLike,
        signature: tuple[Obj, Obj] | None,
    ) -> Mor: ...
    @overload
    def mor(
        self, name: str, cell: MorLike,
        signature: tuple[Obj, Mor],
    ) -> tuple[Mor, Callable[[EqLike], Eq]]: ...
    @overload
    def mor(
        self, name: str, cell: MorLike,
        signature: tuple[Mor, Obj],
    ) -> tuple[Mor, Callable[[EqLike], Eq]]: ...
    @overload
    def mor(
        self, name: str, cell: MorLike,
        signature: tuple[Mor, Mor],
    ) -> tuple[Mor, Callable[[EqLike], Eq]]: ...

    def mor(
        self, name: str, cell: MorLike,
        signature: tuple[Obj | Mor, Obj | Mor] | None = None,
    ):
        """Sets name on morphism and checks signature"""
        if isinstance(cell, Obj):
            cell = cell.identity()

        if not signature:
            # Here `cell` can't be a transformation. A composition with
            # transformations can only be checked after providing a source.
            # For this and other reasons, it makes sense to not make
            # transformation part of the theory the way morphisms are.
            if isinstance(cell, Transformation):
                raise TypeError(
                    "If `cell` is transformation, signature is needed.",
                )

            self._set_name(name, cell)
            return cell

        source, target = signature
        if isinstance(source, Obj):
            if isinstance(cell, Transformation):
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

        if isinstance(cell, Transformation):
            cell = cell(source.source)

        return self._hat_mor(
            name, cell, (source.source, target.source), (source, target),
        )

    def _hat_mor(
        self, name: str, cell: Mor,
        signature: tuple[Obj, Obj], hat_signature: tuple[Mor, Mor],
    ) -> tuple[Mor, Callable[[EqLike], Eq]]:
        """Sets name on morphism and checks signature"""
        source, target = signature
        cell = _fit_mor(source, target, cell)
        hat_source, hat_target = hat_signature

        def _hat(c: EqLike):
            # We defer assigning hat, because we may end up needing cell in its
            # definition.
            return self.eq(
                f'^{name}', c, (hat_source, hat_target.compose(cell)),
            )

        self._set_name(name, cell)
        return cell, _hat

    def eq(
        self, name: str, cell: EqLike,
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
        if isinstance(cell, Obj):
            cell = cell.identity()

        if isinstance(cell, Mor):
            cell = cell.ref()

        if not ssignature:
            if isinstance(cell, Callable):
                raise TypeError(
                    "If `cell` is transformation or law, setoid signature is "
                    "needed.",
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
            # There is no assumption about source being preserved here.
            cell = cell(ssource.source)

            if isinstance(cell, Mor):
                cell = cell.ref()

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

def _gen_fit_mors(source: Obj, factors: Iterator[MorLike]):
    # Adapt the sources of morphisms
    for f in factors:
        f = _source_fit_mor_like(source, f)
        source = f.target
        yield f

def _gen_fit_eqs(source: Obj, factors: Iterator[EqLike]):
    # Adapt the sources of equalities
    for f in factors:
        if isinstance(f, Eq | Law):
            f = _source_fit_eq_or_law(source, f)
            source = f.ssource.target
            yield f
        else:
            f = _source_fit_mor_like(source, f)
            source = f.target
            yield f.ref()

def _cell_source(cell: cells.Cell):
    if isinstance(cell, Obj):
        return cell

    if isinstance(cell, Mor):
        return cell.source

    return cell.ssource.source

def _obj_or_mor_to_mor(cell: Obj | Mor):
    if isinstance(cell, Obj):
        cell = cell.identity()

    return cell

def _mor_like_to_mor(source: Obj, cell: MorLike):
    if isinstance(cell, Callable):
        cell = cell(source)

    return _obj_or_mor_to_mor(cell)

def _cell_to_eq(cell: cells.Cell):
    if isinstance(cell, Obj):
        cell = cell.identity()

    if isinstance(cell, Mor):
        cell = cell.ref()

    return cell

def _eq_like_to_eq(source: Obj, cell: EqLike):
    if isinstance(cell, Callable):
        cell = cell(source)

    return _cell_to_eq(cell)

def _gen_fit_eqs_for_trans(factors: Iterator[Eq]):
    # Conversion is done adapting target from right to left.
    for f in factors:
        f = f
        ssource = f.starget
        yield f
        break
    else:
        assert False

    for f in factors:
        f = _ssource_fit_eq(ssource, f)
        ssource = f.starget
        yield f

def _mor_compose(comp: Composer[Mor], factors: Iterator[Mor]):
    args = list(factors)

    # Discard LazyComposition, it is just for type checking.
    res = reduce(comp, iter(args))
    if res.depth > 5:
        return Composition.simplified(*list(reversed(args)))

    return res.expanded()

def _all_eq_or_law(
    factors: Sequence[EqLike],
) -> TypeGuard[Sequence[Eq | Law]]:
    return all(isinstance(f, Eq | Law) for f in factors)

def _all_mor_like(
    factors: Sequence[EqLike],
) -> TypeGuard[Sequence[MorLike]]:
    return all(isinstance(f, MorLike) for f in factors)

def _all_cell(factors: Sequence[EqLike]) -> TypeGuard[Sequence[cells.Cell]]:
    return all(isinstance(f, cells.Cell) for f in factors)

def _all_obj_or_mor(factors: Sequence[MorLike]) -> TypeGuard[Sequence[Obj | Mor]]:
    return all(isinstance(f, Obj | Mor) for f in factors)

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
        @Transformation
        def _comp(source: Obj):
            # This allows having more than one transformation in factors.
            return _mor_compose(
                comp, _gen_fit_mors(source, factor_it),
            )

        return _comp

    if isinstance(last, Obj):
        source = last
    else:
        source = last.source

    return _mor_compose(comp, _gen_fit_mors(source, factor_it))

def _compose_eq(
    comp: Composer[Eq],
    first: EqLike,
    factors: Sequence[EqLike],
) -> Eq | Law:
    if factors:
        last = factors[-1]
    else:
        last = first

    if isinstance(last, Callable):
        @Law
        def _comp(source: Obj):
            factor_it = chain(reversed(factors), (first,))
            return reduce(comp, _gen_fit_eqs(source, factor_it))

        return _comp

    if isinstance(last, Obj):
        source = last
    elif isinstance(last, Mor):
        source = last.source
    else:
        source = last.ssource.source

    factor_it = chain(reversed(factors), (first,))
    return reduce(comp, _gen_fit_eqs(source, factor_it))

def operate_mor_or_eq(
    op_mor: Callable[[MorLike, Sequence[MorLike]], Mor | Transformation],
    op_eq: Callable[[EqLike, Sequence[EqLike]], Eq | Law],
    first: EqLike, factors: Sequence[EqLike],
):
    """Handle variadic operation for morphisms and equalities"""
    if isinstance(first, Eq | Law):
        return op_eq(first, factors)

    if _all_eq_or_law(factors):
        return op_eq(first, factors)

    assert _all_mor_like(factors)
    return op_mor(first, factors)

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
    ) -> Eq | Law:
        return _compose_eq(comp_eq, first, factors)

    @overload
    def compose(first: MorLike, *factors: MorLike) -> Mor | Transformation: ...
    @overload
    def compose(first: Eq | Law, *factors: EqLike) -> Eq | Law: ...
    @overload
    def compose(first: MorLike, *factors: Eq | Law) -> Eq | Law: ...

    def compose(
        first: EqLike, *factors: EqLike,
    ) -> Mor | Transformation | Eq | Law:
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

def _same_source(first: cells.Cell, factors: Sequence[cells.Cell]):
    source = _cell_source(first)
    return all(_cell_source(f).identical(source) for f in factors)

def operate_mor_common_source(
    op: Callable[[Iterator[Mor]], Mor],
    first: MorLike, factors: Sequence[MorLike],
    rev: bool = False,
):
    """Handle operation on morphisms where common source is expected"""
    if (
        isinstance(first, Obj | Mor) and _all_obj_or_mor(factors)
        and _same_source(first, factors)
    ):
        factor_it = (
            _obj_or_mor_to_mor(x)
            for x in _sequence_to_iterator(first, factors, rev)
        )
        return op(factor_it)

    @Transformation
    def _t(source: Obj):
        factor_it = (
            _mor_like_to_mor(source, x)
            for x in _sequence_to_iterator(first, factors, rev)
        )
        return op(factor_it)

    return _t

def operate_eq_common_source(
    op: Callable[[Iterator[Eq]], Eq],
    first: EqLike, factors: Sequence[EqLike],
    rev: bool = False,
):
    """Handle operation on equalities where common source is expected"""
    if (
        isinstance(first, cells.Cell) and _all_cell(factors)
        and _same_source(first, factors)
    ):
        factor_it = (
            _cell_to_eq(x)
            for x in _sequence_to_iterator(first, factors, rev)
        )
        return op(factor_it)

    @Law
    def _t(source: Obj):
        factor_it = (
            _eq_like_to_eq(source, x)
            for x in _sequence_to_iterator(first, factors, rev)
        )
        return op(factor_it)

    return _t

def _sequence_to_iterator[T](
    first: T, factors: Sequence[T], rev: bool,
) -> Iterator[T]:
    if rev:
        return chain(reversed(factors), (first,))

    return chain((first,), factors)

def _trans(
    trans_: Composer[Eq], first: EqLike, factors: Sequence[EqLike],
) -> Eq | Law:
    def op(it: Iterator[Eq]):
        return reduce(trans_, _gen_fit_eqs_for_trans(it))

    return operate_eq_common_source(op, first, factors, rev=True)

def transitivity(ctx: Context):
    """Create function for variadic high-level composition"""
    trans_ = ctx.trans

    def trans(first: EqLike, *factors: EqLike):
        return _trans(trans_, first, factors)

    return trans
