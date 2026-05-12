# pylint: disable=C0103, R0902, R0914, C0115, C0114
from dataclasses import dataclass
from typing import Self

from wlex.ambient.category import (
    Obj, Mor, Eq as MetaEq, Theory, TheoryStub,
    MorStub, EqStub,
)
from wlex.ambient.category import one as _
from wlex.ambient.lex import LexContext
from .quiver import BasicQuiver, BasicQuiverStub

@dataclass
class LexStub(TheoryStub):
    C: