"""High level interface to category ambient"""
from collections.abc import Callable, Iterator, Sequence
from abc import ABCMeta, abstractmethod
from typing import Any, Self, TypeGuard, TypeVar, overload

from .cells import Obj, Mor, Eq
from .cells.category import Composition
from . import cells
from .public import category as public

Transformation = Callable[[Obj], Mor]
MorLike = Mor | Obj | Transformation

def _fit_mor(source: Obj, target: Obj, cell: Mor):
    # Subclasses of `Obj` can support specific type conversions. Handling of
    # transformations occurs before this (in which case no fitting is
    # needed).
    try:
        sconv = source.conversion(cell.source)
    except cells.ObjUnfit as err:
        raise cells.SourceUnfit("Can't convert", err.frm, err.to) from err

    try:
        tconv = cell.target.conversion(target)
    except cells.ObjUnfit as err:
        raise cells.TargetUnfit("Can't convert", err.frm, err.to) from err

    # This will be just `cell` when `tconv` as `sconv` are identities.
    return tconv.compose(cell).compose(sconv)

def _source_fit_mor_like(source: Obj, cell: MorLike):
    if isinstance(cell, Callable):
        return cell(source)

    if isinstance(cell, Obj):
        cell = cell.identity()

    try:
        sconv = source.conversion(cell.source)
    except cells.ObjUnfit as err:
        raise cells.SourceUnfit(
            "Can't convert for fitting source", err.frm, err.to,
        ) from err

    return cell.compose(sconv)

def _source_fit_eq(source: Obj, cell: Eq):
    try:
        sconv = source.conversion(cell.ssource.source)
    except cells.ObjUnfit as err:
        raise cells.SourceUnfit(
            "Can't convert for fitting source", err.frm, err.to,
        ) from err

    return cell.compose_eq(sconv.ref())

def _fit_eq(ssource: 'Mor', starget: 'Mor', cell: Eq):
    prev_err = None
    for i in range(2):
        try:
            try:
                sconv = ssource.conversion(cell.ssource)
            except cells.MorUnfit as err:
                raise cells.SSourceUnfit("Can't convert", err.frm, err.to) from err

            try:
                tconv = cell.starget.conversion(starget)
            except cells.MorUnfit as err:
                raise cells.STargetUnfit("Can't convert", err.frm, err.to) from err
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
    """Provides methods for naming cells of a theory"""
    __slots__ = ('name_stack',)
    name_stack: tuple[str, ...]

    compose = staticmethod(public.compose)
    compose_eq = staticmethod(public.compose_eq)
    trans = staticmethod(public.trans)
    identity = staticmethod(public.identity)
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
    ) -> tuple[Mor, Callable[[cells.Cell], Eq]]: ...
    @overload
    def mor(
        self, name: str, cell: MorLike | None,
        signature: tuple[Mor, Obj],
    ) -> tuple[Mor, Callable[[cells.Cell], Eq]]: ...
    @overload
    def mor(
        self, name: str, cell: MorLike | None,
        signature: tuple[Mor, Mor],
    ) -> tuple[Mor, Callable[[cells.Cell], Eq]]: ...

    def mor(
        self, name: str, cell: MorLike | None,
        signature: tuple[Obj | Mor, Obj | Mor] | None = None,
    ):
        """Sets name on morphism and checks signature"""
        if not cell:
            raise ValueError(f'Missing cell "{name}"')

        if isinstance(cell, Obj):
            cell = cell.identity()

        if signature is None:
            # Here `cell` can't be a transformation. A composition with
            # transformation can only be checked after providing a source.
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
            # `source`.
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
    ) -> tuple[Mor, Callable[[cells.Cell], Eq]]:
        """Sets name on morphism and checks signature"""
        source, target = signature

        cell = _fit_mor(source, target, cell)

        hat_source, hat_target = hat_signature

        def _hat(c: cells.Cell):
            # We defer assigning hat, because we may end up needing cell in its
            # definition.
            return self.eq(
                f'^{name}', c, (hat_source, hat_target.compose(cell)),
            )

        self._set_name(name, cell)
        return cell, _hat

    def eq(
        self, name: str, cell: cells.Cell | None,
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
                "When no signature is provided, at least one of `ssource` "
                "and `starget` must be a morphism.",
            )

        cell = _fit_eq(ssource, starget, cell)
        self._set_name(name, cell)
        return cell

# In wlex syntax signature is required to occur before invocation.
# Definition can occur after invocation.
# In python definition occurs along with signature.
# Primitives get defined by assigning param.
# Category operations (ambient) are defined globally (even if dynamic),
# not as methods.
# There can be a context class for cart which supports method el besides method mor.

ComposableT = TypeVar('ComposableT')
Composer = Callable[[tuple[ComposableT, ComposableT]], ComposableT]

def _cell_compose[T](comp: Composer[T], factors: Iterator[T]) -> T:
    acc: T | None = None
    for f in factors:
        acc = f
        break
    else:
        assert False

    for f in factors:
        acc = comp((f, acc))

    return acc

def _gen_fit_mors(source: Obj, factors: Sequence[MorLike]):
    for f in reversed(factors):
        f = _source_fit_mor_like(source, f)
        source = f.source
        yield f

def _gen_fit_eqs(source: Obj, factors: Sequence[MorLike | Eq]):
    for f in reversed(factors):
        if isinstance(f, Eq):
            f = _source_fit_eq(source, f)
            source = f.ssource.target
            yield f
        else:
            f = _source_fit_mor_like(source, f)
            source = f.source
            f = f.ref()
            yield f

def _mor_compose(comp: Composer[Mor], factors: Iterator[Mor]):
    args = list(factors)
    # Discard the LazyComposition, it is just for type checking.
    _cell_compose(comp, iter(args))
    return Composition.simplified(*args)

def all_morlike(
    factors: Sequence[MorLike | Eq],
) -> TypeGuard[Sequence[MorLike]]:
    return all(not isinstance(f, Eq) for f in factors)

def _compose(
    comp: Composer[Mor], comp_eq: Composer[Eq],
    factors: Sequence[MorLike | Eq],
) -> Mor | Transformation | Eq:
    if not factors:
        raise ValueError("Empty composition is not allowed.")

    # TODO: First convert all obj to mor

    if all_morlike(factors):
        last = factors[-1]

        if isinstance(last, Callable):
            def _comp(source: Obj):
                # This allows having more than one transformation in factors.
                return _mor_compose(comp, _gen_fit_mors(source, factors))

            return _comp

        if isinstance(last, Obj):
            last = last.identity()

        return _mor_compose(comp, _gen_fit_mors(last.source, factors))

    last = factors[-1]
    if isinstance(last, Callable):
        # Transformation has no `ref`.
        raise TypeError(
            "Transformation is not allowed as the last factor of a composition "
            "containing equalities."
        )

    if isinstance(last, Obj):
        last = last.identity()

    if isinstance(last, Mor):
        last = last.ref()

    return _cell_compose(comp_eq, _gen_fit_eqs(last.ssource.source, factors))

def composer(ctx: Context):
    """Creates function for variadic high-level composition"""
    def _all_morlike_or_eq(
        factors: Sequence[MorLike | Eq | None],
    ) -> TypeGuard[Sequence[MorLike | Eq]]:
        return all(factors)

    comp = ctx.compose
    comp_eq = ctx.compose_eq

    @overload
    def compose(*factors: MorLike) -> Mor | Transformation: ...
    @overload
    def compose(*factors: Eq) -> Eq: ...
    @overload
    def compose(*factors: MorLike | Eq | None) -> Any: ...

    def compose(*factors: MorLike | Eq | None):
        if _all_morlike_or_eq(factors):
            return _compose(comp, comp_eq, factors)

        raise ValueError("Missing factor")

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

def _trans(trans_: Composer[Eq], factors: Sequence[cells.Cell]) -> Eq:
    args = (
        m.identity().ref() if isinstance(m, Obj) else (
            m.ref() if isinstance(m, Mor) else m
        ) for m in factors
    )
    # TODO: Use ssource conversion?
    return _cell_compose(trans_, args)

def transitivity(ctx: Context):
    """Creates function for variadic high-level composition"""
    def _all_cell(
        factors: Sequence[cells.Cell | None],
    ) -> TypeGuard[Sequence[cells.Cell]]:
        return all(factors)

    trans_ = ctx.trans

    def trans(*factors: cells.Cell | None):
        if _all_cell(factors):
            return _trans(trans_, factors)

        raise ValueError("Missing Factor")

    return trans
