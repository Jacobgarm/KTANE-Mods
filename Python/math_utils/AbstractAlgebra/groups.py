from __future__ import annotations
import math_utils.NumberTheory as nt
from helpers import *
from dataclasses import dataclass
from itertools import product
from collections import Counter


class GroupElement(Element):
    parent: Group

    def __add__(self, other):
        assert self.parent is other.parent
        return self.parent.compose(self, other)

    def __neg__(self):
        return self.parent.invert(self)

    def __sub__(self, other):
        return self + (-other)

    def order(self):
        a = self
        m = 1
        while a != self.parent.identity:
            m += 1
            a += self
        return m

    def is_involution(self):
        return self + self == self.parent.identity


def commutator(a, b):
    return (-a) + (-b) + a + b


class Group:
    elements: frozenset[GroupElement]
    identity: GroupElement
    composition: Callable[[GroupElement, GroupElement], GroupElement]
    inverse: Callable[[GroupElement], GroupElement]
    name: str

    def __init__(self, elems, id, comp, inv, nam="Group"):
        if not isinstance(next(iter(elems)), GroupElement):
            elems = frozenset(GroupElement(e, self) for e in elems)
        self.elements = elems
        if not isinstance(id, GroupElement):
            id = GroupElement(id, self)
        self.composition = comp
        self.identity = id
        self.inverse = inv
        self.name = nam

    def __call__(self, obj) -> GroupElement:
        elem = GroupElement(obj, self)
        assert elem in self.elements
        return elem

    def compose(self, a: GroupElement, b: GroupElement) -> GroupElement:
        return GroupElement(self.composition(a.value, b.value), self)

    def invert(self, e: GroupElement) -> GroupElement:
        return GroupElement(self.inverse(e.value), self)

    def order(self) -> int:
        return len(self.elements)

    def __len__(self):
        return self.order()

    def values(self) -> frozenset:
        return frozenset(g.value for g in self.elements)

    def check_closure(self) -> bool:
        for a in self.elements:
            for b in self.elements:
                if a + b not in self.elements:
                    return False
        return True

    def check_associativity(self) -> bool:
        for a in self.elements:
            for b in self.elements:
                for c in self.elements:
                    if a + (b + c) != (a + b) + c:
                        return False
        return True

    def check_inverses(self) -> bool:
        for e in self.elements:
            if e - e != self.identity:
                print(e)
                return False
        return True

    def check_identity(self) -> bool:
        for e in self.elements:
            if e + self.identity != e or self.identity + e != e:
                return False
        return True

    def check_all(self) -> bool:
        return (
            self.check_closure()
            and self.check_associativity()
            and self.check_inverses()
            and self.check_identity()
        )

    def is_trivial(self):
        return self.order() == 1

    def is_abelian(self) -> bool:
        for a in self.elements:
            for b in self.elements:
                if a + b != b + a:
                    return False
        return True

    def subgroup(self, elements):
        if isinstance(next(iter(elements)), GroupElement):
            elements = frozenset(map(lambda g: g.value, elements))
        return Group(elements, self.identity.value, self.composition, self.inverse)

    def is_subgroup(self, parent: Group) -> bool:
        return self.elements <= parent.elements

    def is_normal_subgroup(self, parent: Group) -> bool:
        if not self.is_subgroup(parent):
            return False
        for g in parent.elements:
            if g * self != self * g:
                return False
        return True

    def orders(self) -> Counter:
        order_counter = Counter()
        for g in self.elements:
            order_counter[g.order()] += 1
        return order_counter

    def trivial_subgroup(self) -> Group:
        return self.subgroup({self.identity})

    def __mul__(self, other):
        if isinstance(other, GroupElement):
            return coset(other, self, other.parent, True)
        elif isinstance(other, Group):
            return direct_product(self, other)
        return NotImplemented

    def __rmul__(self, other):
        if isinstance(other, GroupElement):
            return coset(other, self, other.parent)
        return NotImplemented

    def automorphisms(self, table: Optional[dict] = None) -> list[dict]:
        if table is None:
            table = {self.identity: self.identity}
        missing_keys = self.elements - frozenset(table.keys())
        missing_values = self.elements - frozenset(table.values())

        elem = next(iter(missing_keys))
        auts = []
        for image in missing_values:
            new_table = table.copy()
            new_table[elem] = image
            news = {(elem, image)}
            contradiction = False
            while news:
                new_elem, new_image = news.pop()
                for other in new_table.copy().keys():
                    left_comp = new_elem + other
                    left_comp_image = new_image + new_table[other]
                    if left_comp in new_table:
                        if new_table[left_comp] != left_comp_image:
                            contradiction = True
                            break
                    elif left_comp_image in new_table.values():
                        contradiction = True
                        break
                    else:
                        new_table[left_comp] = left_comp_image
                        news.add((left_comp, left_comp_image))

                    right_comp = other + new_elem
                    right_comp_image = new_table[other] + new_image
                    if right_comp in new_table:
                        if new_table[right_comp] != right_comp_image:
                            contradiction = True
                            break
                    else:
                        new_table[right_comp] = right_comp_image
                        news.add((right_comp, right_comp_image))

                if contradiction:
                    break

            if contradiction:
                continue

            if len(new_table) == self.order():
                auts.append(new_table)

            else:
                auts.extend(self.automorphisms(new_table))

        return auts

    def automorphism_group(self):
        return Group(
            frozenset(Morphism(table, self, self) for table in self.automorphisms()),
            identity_morphism(self),
            compose_morphisms,
            inverse_morphism,
        )

    def center(self) -> frozenset:
        cent = set()
        for x in self.elements:
            for g in self.elements:
                if g + x != x + g:
                    break
            else:
                cent.add(x)
        return frozenset(cent)

    def center_group(self) -> Group:
        return Group(
            frozenset({z.value for z in self.center()}),
            self.identity.value,
            self.composition,
            self.inverse,
            "Center group",
        )

    def quotient_group(self, H: Group) -> Group:
        assert H.is_normal_subgroup(
            self
        ), "Quotient groups can only be made from normal subgroups"
        cosets = set()
        for g in self.elements:
            cosets.add(g * H)
        return Group(
            frozenset(cosets),
            frozenset(self(h) for h in H.values()),
            compose_cosets,
            inverse_coset,
        )

    def __truediv__(self, other: Group) -> Group:
        return self.quotient_group(other)

    def commutator_subgroup(self, subgroup: Optional[Group] = None) -> Group:
        if subgroup is None:
            subgroup = self
        subvals = subgroup.values()
        commutators = set()
        for a in self.elements:
            for b in self.elements:
                if b.value in subvals:
                    commutators.add(commutator(a, b))
        return self.generate_subgroup(frozenset(commutators))

    def derived_series(self) -> list[Group]:
        series = [self]
        while series[-1].order() != 1:
            derived_group = series[-1].commutator_subgroup()
            if series[-1].order() == derived_group.order():
                break
            series.append(derived_group)
        return series

    def is_perfect(self) -> bool:
        return self == self.commutator_subgroup()

    def is_solvable(self) -> bool:
        return self.derived_series()[-1].is_trivial()

    def lower_central_series(self) -> list[Group]:
        series = [self]
        while True:
            commutator_subgroup = self.commutator_subgroup(series[-1])
            if series[-1].order() == commutator_subgroup.order():
                break
            series.append(commutator_subgroup)
        return series

    def upper_central_series(self) -> list[Group]:
        series = [self.trivial_subgroup()]
        while True:
            next_center = set(series[-1].values())
            for x in self.elements:
                if x.value in next_center:
                    continue
                for y in self.elements:
                    if commutator(x, y).value not in series[-1].values():
                        break
                else:
                    next_center.add(x.value)
            center_group = self.subgroup(next_center)
            if series[-1].order() == center_group.order():
                break
            series.append(center_group)
        return series

    def is_nilpotent(self) -> bool:
        return self.lower_central_series()[-1].is_trivial()

    def nilpotency(self) -> int:
        return len(self.lower_central_series())

    def abelianization(self) -> Group:
        return self / self.commutator_subgroup()

    def opposite_group(self) -> Group:
        return Group(
            self.values(),
            self.identity.value,
            lambda a, b: self.composition(b, a),
            self.inverse,
        )

    def involutions(self) -> frozenset[GroupElement]:
        return frozenset(g for g in self.elements if g.is_involution())

    def cayley_table(self, names=None, ordering=None):
        if names is None:
            names = {}
            names[self.identity] = "e"
            for i, a in enumerate(self.elements - {self.identity}):
                names[a] = chr(i + 97 + (i > 3))

        if ordering is None:
            ordering = [self.identity] + [e for e in self.elements - {self.identity}]

        for e in ordering:
            print(f"{names[e]} is {str(e)}")
        print()
        name_width = max(len(str(n)) for n in names.values())
        width = 1 + (name_width + 1) * len(ordering)
        print(
            " " * name_width
            + "|"
            + " ".join(names[e].rjust(name_width) for e in ordering)
        )
        print("-" * name_width + "+" + "-" * (width - 2))
        for a in ordering:
            s = names[a].rjust(name_width) + "|"
            s += " ".join(names[a + b].rjust(name_width) for b in ordering)
            print(s)
            print(" " * name_width + "|")

    def interactive_cayley(self):
        names = {}
        for e in self.elements:
            print(f"Name for {e}:")
            names[e] = input()
        print()
        unordered = set(self.elements)
        ordering = []
        print(f"Assuming identity {names[self.identity]} is first")
        ordering.append(self.identity)
        unordered.remove(self.identity)
        while len(unordered) > 1:
            print("What is the next element?")
            name = input()
            for k, v in names.items():
                if v == name:
                    ordering.append(k)
                    unordered.remove(k)
                    break
            else:
                print("No such element found")
        last = next(iter(unordered))
        print(f"And last element must then be {names[last]}")
        ordering.append(last)

        self.cayley_table(names, ordering)

    def generate_subgroup(self, subset: frozenset) -> Group:
        if isinstance(next(iter(subset)), GroupElement):
            generators = frozenset(subset)
        else:
            generators = frozenset(GroupElement(e, self) for e in subset)
        unvisited = set(generators)
        visited = set()
        while unvisited:
            x = unvisited.pop()
            for e in generators:
                l = e + x
                if l not in visited:
                    unvisited.add(l)
                r = x + e
                if r not in visited:
                    unvisited.add(r)
            visited.add(x)
        return Group(
            frozenset(e.value for e in visited),
            self.identity.value,
            self.composition,
            self.inverse,
            "Generated subgroup",
        )

    def is_generating_set(self, subset):
        return self.generate_subgroup(subset).order() == self.order()

    def __str__(self) -> str:
        return f"{self.name} of order {self.order()}"

    def __repr__(self) -> str:
        return str(self)


def trivial_group() -> Group:
    return Group(frozenset({0}), 0, lambda a, _: a, lambda x: x, "Trivial group")


def symmetric_group(n: int) -> Group:
    id = nperm(n)
    return Group(
        permutations(id),
        id,
        compose_permutations,
        inverse_permutation,
        "Symmetric group",
    )


def alternating_group(n: int) -> Group:
    id = nperm(n)
    return Group(
        frozenset(p for p in permutations(id) if permutation_is_even(p)),
        id,
        compose_permutations,
        inverse_permutation,
        "Alternating Group",
    )


def cyclic_group(n: int) -> Group:
    return Group(
        nset(n), 0, lambda a, b: (a + b) % n, lambda a: (-a) % n, "Cyclic group"
    )


def coprime_group(n: int) -> Group:
    return Group(
        nt.coprimes(n), 1, lambda a, b: (a * b) % n, lambda x: nt.get_inverse_mod(x, n)
    )


def dihedral_group(n: int) -> Group:
    rots = {("r", Fraction(i, n)) for i in range(n)}
    flips = {("f", Fraction(i, 2 * n)) for i in range(n)}
    return Group(
        frozenset(rots | flips),
        ("r", Fraction(0)),
        compose_transformations,
        inverse_transformation,
        "Dihedral group",
    )


def dicyclic_group(n: int) -> Group:
    return Group(
        frozenset((a, x) for a in range(0, 2 * n) for x in (0, 1)),
        (0, 0),
        lambda a, b: compose_dics(n, a, b),
        lambda a: inverse_dic(n, a),
        "Dicyclic group",
    )


def compose_dics(n, a, b):
    if a[1] == 0:
        return ((a[0] + b[0]) % (2 * n), b[1])
    else:
        return ((a[0] - b[0] + n * b[1]) % (2 * n), 1 - b[1])


def inverse_dic(n, a):
    if a[1] == 0:
        return (2 * n - a[0], 0)
    else:
        return ((a[0] + n) % (2 * n), 1)


def coset(g: GroupElement, H: Group, G: Group, right=False) -> frozenset[GroupElement]:
    assert H.is_subgroup(G), "Cosets can only be constructed from subgroups"
    cos = set()
    for h in H.elements:
        if right:
            cos.add(G(h.value) + g)
        else:
            cos.add(g + G(h.value))
    return frozenset(cos)


def compose_cosets(X: frozenset[GroupElement], Y: frozenset[GroupElement]):
    cos = set()
    for x in X:
        for y in Y:
            cos.add(x + y)
    return frozenset(cos)


def inverse_coset(X: frozenset[GroupElement]):
    cos = set()
    for x in X:
        cos.add(-x)
    return frozenset(cos)


def direct_product(G: Group, H: Group):
    return Group(
        frozenset(product(G.values(), H.values())),
        (G.identity.value, H.identity.value),
        lambda p1, p2: (G.composition(p1[0], p2[0]), H.composition(p1[1], p2[1])),
        lambda p: (G.inverse(p[0]), H.inverse(p[1])),
        "Direct product group",
    )


@dataclass
class Morphism:
    table: dict[GroupElement, GroupElement]
    domain: Group
    codomain: Group

    @classmethod
    def from_func(cls, func, domain, codomain):
        table = {}
        for x in domain.elements:
            table[x] = func(x)
        return cls(table, domain, codomain)

    def __call__(self, e: GroupElement) -> GroupElement:
        assert e in self.domain.elements, "Argument must be in domain of morphism"
        return self.table[e]

    def __hash__(self):
        return hash(tuple(self.table.items()))
        return hash(tuple(sorted((k.value, v.value) for k, v in self.table.items())))

    def is_homo(self) -> bool:
        for a in self.domain.elements:
            for b in self.domain.elements:
                if self(a + b) != self(a) + self(b):
                    print(a)
                    print(b)
                    print(a + b)
                    print(self(a))
                    print(self(b))
                    print(self(a + b))
                    print(self(a) + self(b))
                    return False
        return True

    def is_endo(self) -> bool:
        return self.domain is self.codomain

    def is_mono(self) -> bool:
        hit = set()
        for x in self.domain.elements:
            y = self(x)
            if y in hit:
                return False
            hit.add(y)
        return True

    def is_epi(self) -> bool:
        hit = {self(x) for x in self.domain.elements}
        return hit == self.codomain.elements

    def is_iso(self) -> bool:
        return self.is_mono() and self.is_epi()

    def is_auto(self) -> bool:
        return self.is_endo() and self.is_iso()

    def __str__(self) -> str:
        return f"Morphism from {self.domain} to {self.codomain}"

    def kernel(self) -> frozenset[GroupElement]:
        ker = set()
        for e in self.domain.elements:
            if self(e) == self.codomain.identity:
                ker.add(e)
        return frozenset(ker)

    def kernel_group(self) -> Group:
        return Group(
            self.kernel(),
            self.domain.identity.value,
            self.domain.composition,
            self.domain.inverse,
            "Kernel group",
        )

    def image(self) -> frozenset[GroupElement]:
        return frozenset(self.table.keys())

    def image_group(self) -> Group:
        return Group(
            self.image(),
            self.codomain.identity.value,
            self.codomain.composition,
            self.codomain.inverse,
            "Image group",
        )


def compose_morphisms(f: Morphism, g: Morphism) -> Morphism:
    assert f.codomain == g.domain
    return Morphism(
        {key: g(value) for key, value in f.table.items()}, f.domain, g.codomain
    )


def inverse_morphism(f: Morphism) -> Morphism:
    assert f.is_iso()
    return Morphism(
        {value: key for key, value in f.table.items()}, f.codomain, f.domain
    )


def trivial_morphism(G: Group, H: Group) -> Morphism:
    return Morphism.from_func(lambda _: H.identity, G, H)


def identity_morphism(G: Group) -> Morphism:
    return Morphism.from_func(
        lambda x: x,
        G,
        G,
    )


def inclusion_morphism(G: Group, H: Group) -> Morphism:
    return Morphism.from_func(lambda x: H(x.value), H, G)


def coset_morphism(G: Group, H: Group) -> Morphism:
    quotient = G / H
    return Morphism.from_func(
        lambda g: quotient(g * H),
        G,
        quotient,
    )


def conjugation_morphism(G: Group, g: GroupElement) -> Morphism:
    return Morphism.from_func(lambda x: g + x + (-g), G, G)


def sgn_morphism(n):
    cyclic_2 = cyclic_group(2)
    return Morphism.from_func(
        lambda g: cyclic_2(0 if permutation_is_even(g.value) else 0),
        symmetric_group(n),
        cyclic_2,
    )


def are_coprime(a: int, b: int) -> bool:
    return cyclic_group(a).generate_subgroup(frozenset({b})).order() == a


# Specific groups

S2 = symmetric_group(2)
S3 = symmetric_group(3)
S4 = symmetric_group(4)
S5 = symmetric_group(5)

A2 = alternating_group(2)
A3 = alternating_group(3)
A4 = alternating_group(4)
A5 = alternating_group(5)

C2 = cyclic_group(2)
C3 = cyclic_group(3)
C4 = cyclic_group(4)
C5 = cyclic_group(5)

D3 = dihedral_group(3)
D4 = dihedral_group(4)

K4 = C2 * C2

Q8 = dicyclic_group(2)

# Specific morphisms

modder = Morphism.from_func(lambda x: C2(x.value % 2), C4, C2)

print()
C12 = cyclic_group(12)
Q = C12 / C12.generate_subgroup(frozenset({4}))
print(Q.check_all())
for e in Q.values():
    print({x.value for x in e})


A = coprime_group(15)

B = C2 * C4


def f(x):
    x = x.value
    y = {
        (C2(0), C4(0)): 1,
        (C2(1), C4(0)): 14,
        (C2(0), C4(1)): 2,
        (C2(0), C4(2)): 4,
        (C2(0), C4(3)): 8,
        (C2(1), C4(1)): 13,
        (C2(1), C4(2)): 11,
        (C2(1), C4(3)): 7,
    }
    return A(y[x])


M = Morphism.from_func(f, B, A)
