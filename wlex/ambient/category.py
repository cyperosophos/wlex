"""High level interface to category ambient"""
from collections.abc import Callable
from abc import ABCMeta, abstractmethod
from typing import Any, Self

from .cells import Name, Obj, Mor, Eq
from . import cells

# class _hat(str):
#     __slots__ = ()

#     def __str__(self):
#         return f'^{super().__str__()}'

#     def __repr__(self):
#         return repr(str(self))

#     def __eq__(self, v: object):
#         return super().__eq__(v) and isinstance(v, _hat)

#     def hash(self):
#         return super().__hash__() + 1

Transformation = Callable[[Obj], Mor]
MorLike = Mor | Obj | Transformation

class _TransformationWrapper:
    __slots__ = ('func',)

    def __init__(self, func: Transformation):
        self.func = func

    def __call__(self, source: Obj):
        return self.func(source)

    def __str__(self):
        return self.func.__name__

    def __repr__(self):
        return f'Transformation("{self!s}")'

def transformation(func: Transformation):
    """Transformation decorator

    A transformation allows obtaining a morphism from an object, which becomes
    the source of the resulting morphism).
    """
    return _TransformationWrapper(func)

# def get_cell[T: cells.Cell](
#     cell_cls: type[T], theory: Theory, name: str,
# ) -> T | None:
#     if name in theory:
#         value = theory[name]
#         if isinstance(value, cell_cls):
#             return value

#         raise TypeError(
#             "Found value of wrong type in base theory (expected "
#             "`{cell_cls.__name__}`)",
#         )
#     return None

# def get_sub(theory: Theory, name: str, ):
#     if name in theory:
#         value = theory[name]
#         if isinstance(value, dict):
#             return value

#         raise TypeError(
#             "Found value of wrong type in base theory (expected `Theory`).",
#         )
#     return None

# def _make_mor(name: Name, source: Mor | Obj, target: Mor | Obj):
#     if isinstance(source, Obj):
#         if isinstance(target, Obj):
#             res = PrimMor(source, target)
#             hat = None
#         else:
#             res = PrimMor(source, target.source)
#             hat = PrimEq(source.identity(), target.compose(res))
#     else:
#         if isinstance(target, Obj):
#             # Object `target` is disallowed here, because it would have the same
#             # effect as setting the value of the morphism being created to
#             # `source`.
#             raise TypeError(
#                 "If `source` is morphism, then so must be `target`.",
#             )
#         else:
#             res = PrimMor(source.source, target.source)
#             hat = PrimEq(source, target.compose(res))

#     res.name = name
#     if hat:
#         hat.name = (*name, _hat(name[-1]))

#     return res, hat

# def _make_eq(name: Name, ssource: MorLike, starget: MorLike):
#     ssource, starget = (
#         m.identity() if isinstance(m, Obj) else m
#         for m in (ssource, starget)
#     )

#     if isinstance(ssource, Mor):
#         if isinstance(starget, Mor):
#             res = PrimEq(ssource, starget)
#         else:
#             res = PrimEq(ssource, starget(ssource.source))
#     else:
#         if isinstance(starget, Mor):
#             res = PrimEq(ssource(starget.source), starget)
#         else:
#             raise TypeError(
#                 "At least one of `ssource` and `starget` must be of type `Mor`."
#             )

#     res.name = name
#     return res


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

def _signature_with_hat(source: Obj | Mor, target: Obj | Mor):
    if isinstance(source, Obj):
        if isinstance(target, Obj):
            return (source, target), None

        return (source, target.source), (source.identity(), target)

    if isinstance(target, Obj):
        # Object `target` is disallowed here, because it would have the same
        # effect as setting the value of the morphism being created to
        # `source`.
        raise TypeError(
            "If `source` is morphism, then so must be `target`.",
        )

    return (source.source, target.source), (source, target)

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

# TODO: primitives can't be changed through conversion!

class Context:
    """Provides methods for naming cells of a theory"""
    __slots__ = ('name_stack',)
    name_stack: tuple[str, ...]

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

    def mor(
        self, name: str, cell: MorLike | None,
        signature: tuple[Obj, Obj] | None = None,
    ):
        """Sets name on morphism and checks signature"""
        if not cell:
            raise ValueError(f'Missing cell "{name}"')

        if isinstance(cell, Obj):
            cell = cell.identity()

        if not signature:
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

        if isinstance(cell, Callable):
            cell = cell(source)

        cell = _fit_mor(source, target, cell)
        self._set_name(name, cell)
        return cell

    def hat_mor(
        self, name: str, cell: MorLike | None,
        signature: tuple[Obj | Mor, Obj | Mor],
    ):
        """Sets name on morphism and checks signature"""
        if not cell:
            raise ValueError(f'Missing cell "{name}"')

        if isinstance(cell, Obj):
            cell = cell.identity()

        (source, target), hat_signature = _signature_with_hat(*signature)

        if isinstance(cell, Callable):
            cell = cell(source)

        cell = _fit_mor(source, target, cell)

        if not hat_signature:
            raise TypeError("Signature must contain at least one morphism.")

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
        # `cell.starget`. Doing composition (besides transitivity) for
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

#class _HatAccessor

# TODO: Just as one applies conversions for fitting morphisms,
# one uses sym for fitting equalities.
# TODO: When creating PrimEq conversions can be used for fitting
# ssource and starget. In fact it seems object conversions can be
# used everywhere transformations are used.

# class Category:
#     theory: Theory
#     _base: Theory
#     name: Name

#     def __init__(self, name: Name = (), base: Theory | None = None):
#         super().__setattr__('_base', base or {})
#         super().__setattr__('name', name)
#         super().__setattr__('theory', {})

#     def __getattr__(self, name: str) -> CellLike:
#         return self.theory[name]

#     def __setattr__(self, name: str, value: CellLike):
#         if name in self.theory:
#             old = self.theory[name]
#             if isinstance(value, cells.Cell):
#                 if not isinstance(old, PrimObj | PrimMor | PrimEq):
#                     raise TypeError("Can't override")

#                 # TODO: What about assigning prim to prim, etc.
#                 value = old.fit_signature(value)

#                 if not hasattr(value, 'name'):
#                     value.name = old.name
#             else: # sub ...
#                 pass

#         self.theory[name] = value

    #eq(<name>=<signature>)

# Make all primitive cells function parameters.
# Instead of PrimMor, implement classes with special eval, etc.
# No lazy sub creation, so no need to explicitly avoid loops.
# In wlex syntax signature is required to occur before invocation.
# Definition can occur after invocation.
# In python definition occurs along with signature.
# Primitives get defined by assigning param.
# Category operations (ambient) are defined globally (even if dynamic),
# not as methods.
# There can be a context class for cart which supports method el besides method mor.
