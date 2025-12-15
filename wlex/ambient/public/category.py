"""Public model of `category` morphisms

Here public means that there is dynamic validation (type checking) of arguments
besides the static type checking supported through type annotations.
"""
from ..private import category
from . import validated

source = category.source
target = category.target

compose = validated(category.compose, category.is_composable)
identity = category.identity
ssource = validated(category.ssource, category.is_eq)
starget = validated(category.starget, category.is_eq)
ref = category.ref
trans = validated(category.trans, category.is_path)
left_identity_law = category.left_identity_law
right_identity_law = category.right_identity_law
associativity = validated(
    category.associativity, category.is_associativity_source,
)
eq_signature = validated(category.eq_signature, category.is_eq)
eq_unique = validated(category.eq_unique, category.is_eq_unique_source)
sym = validated(category.sym, category.is_eq)
compose_eq = validated(category.compose_eq, category.is_composable_eq)
