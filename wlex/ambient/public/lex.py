"""Public model of `lex` morphisms"""
from ..private import lex
from . import validated

equalizer = validated(lex.equalizer, lex.is_parallel)
equalizer_pairing = validated(lex.equalizer_pairing, lex.is_fork)
equalizer_pairing_unique = validated(
    lex.equalizer_pairing_unique, lex.is_equalizer_mor
)
