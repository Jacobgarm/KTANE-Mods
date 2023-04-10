from __future__ import annotations
from typing import Callable, Any, Optional
from numbers import Real
from fractions import Fraction
from linalg import Matrix

Permutation = tuple[int, ...]
Transformation = tuple[str, Real]


def compose_permutations(p: Permutation, q: Permutation) -> Permutation:
    newperm = [p[i] for i in q]
    return tuple(newperm)


def inverse_permutation(p: Permutation) -> Permutation:
    newperm = [0 for i in range(0, len(p))]
    for i, a in enumerate(p):
        newperm[a] = i
    return tuple(newperm)


def inversions(p: Permutation) -> int:
    return sum(
        1 if p[i] > p[j] else 0 for i in range(0, len(p) - 1) for j in range(i, len(p))
    )


def permutation_is_even(p: Permutation) -> bool:
    return inversions(p) % 2 == 0


def permutations(p: Permutation) -> frozenset[Permutation]:
    if len(p) == 1:
        return frozenset({p})
    s: frozenset[Permutation] = frozenset()
    for e in p:
        subset = tuple(a for a in p if a != e)
        subsym = permutations(subset)
        s |= frozenset((e,) + subperm for subperm in subsym)
    return s


def powerset(s: frozenset) -> frozenset[frozenset]:
    return frozenset(frozenset())


def nset(n: int) -> frozenset:
    return frozenset(range(n))


def nperm(n: int) -> Permutation:
    return tuple(range(n))


def compose_transformations(a: Transformation, b: Transformation) -> Transformation:
    if a[0] == b[0] == "r":
        return ("r", (a[1] + b[1]) % 1)
    elif a[0] == b[0] == "f":
        return ("r", (b[1] - a[1]) * 2 % 1)
    elif a[0] == "r" and b[0] == "f":
        return ("f", (b[1] - a[1] / 2) % Fraction(1, 2))
    else:
        return ("f", (a[1] + b[1] / 2) % Fraction(1, 2))


def inverse_transformation(x: Transformation) -> Transformation:
    if x[0] == "r":
        return ("r", (1 - x[1]) % 1)
    else:
        return x


class Element:
    value: Any
    parent: Any

    def __init__(self, val, par):
        self.value = val
        self.parent = par

    def singleton(self) -> frozenset[Self]:
        return frozenset({self})

    def __repr__(self) -> str:
        return f"Element {self.value} of {self.parent}"

    def __str__(self) -> str:
        if isinstance(self.value, tuple):
            return f"({', '.join(str(x) for x in self.value)})"
        return str(self.value)

    def __hash__(self):
        return hash(self.value)

    def __eq__(self, other):
        if isinstance(other, Element):
            return self.value == other.value
        return self.value == other
