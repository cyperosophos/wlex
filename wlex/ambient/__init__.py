#from .cells import Obj, Mor, Eq
#from typing import Any

# Recall computational cheating:
# All functions are computable (they have an eval method).
# Not all types have computable equality (check_eq method),
# in other words equality in a homset whose domain is the
# point, just like in all other homsets, is in general not
# decidable. Eval simply gives a canonical encoding of a
# function from the point. Notice that Eq.verify may fail
# regardles of the Eq instance having a proof.

# TODO: Two product types are equal when they have the same
# types as components with the same names in the same order,
# i.e. same params. Otherwise, they may still be isomorphic.
# It makes sense then that equality for instances of sequence
# classes that are treated as instance of products should be
# true even when the classes don't coincide. Such equality
# may have to be intensionally proven (as equality of morphisms
# from the point). For equalizers one has inclusions, which
# the equalities would still follow. Notice however that in the
# case of intensional equalities, the morphisms must have the
# same signature. So this would not work with inclusion.
# Nothing needs to be done with NamedTuple.
# TODO: Actually, a much more simple and reliable approach is
# to forgo using __eq__ altogether. Instead when comparing for
# (extensional) equality one calls a method specific to the class
# (so there would be Mor.eq_mor and ProductMor.eq_product_mor).
# This also make sense considering that we are raising TypeError
# in the equality comparison, whereas __eq__ applies to any type.
# In some cases it makes sense to simply use __eq__ (such as in
# the case of NamedTuple), and one may in fact have ProductMor.__eq__
# since there is never the need to subclass a Sequence type.
# Solution is to have an __eq__ that acts according to the type
# of the arg? No because both self and x may be ProductMor in a
# context where Mor.__eq__ is required.
# Solution is to always explicitly use __eq__ belonging to a particular class?
# This is overkill. The ambiguity of which __eq__ to use only occurs
# when a Sequence inherits from an non Sequence (e.g. a cell like Mor).
# The solution is then to provide a secondary comparison in this cases.
# The full sequence comparison is by far the less common case.
# It is needed for example in Eq.verify.
# Multiple inheritance is not supported, since the ambiguity would not be
# resolvable when comparing two instances that inherit multiply in the same way.
# (Multiple) implicit inheritance from Sequence types is supported.
#type(self).mro()[1]
# This also may solve the issue of comparing sequences of different types.
# if not isinstance(x, Sequence):
#     raise TypeError
# if not isinstance(y, Sequence):
#     raise TypeError