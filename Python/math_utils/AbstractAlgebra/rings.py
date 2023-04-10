from __future__ import annotations

from linalg import Matrix
from groups import *


class RingElement(Element):
    parent: Ring

    def __add__(self, other):
        assert self.parent is other.parent
        return self.parent.add(self, other)

    def __neg__(self):
        return self.parent.negate(self)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        if isinstance(other, int):
            if other < 0:
                s = -self
                other = -other
            else:
                s = self
            x = self.parent.additive_identity
            for _ in range(other):
                x = x + s
            return x
        assert self.parent is other.parent
        return self.parent.multiply(self, other)

    def __rmul__(self, other):
        return self * other

    def __invert__(self):
        return self.parent.reciprocal(self)

    def __truediv__(self, other):
        return self * (~other)

    def __pow__(self, other: int):
        if other < 0:
            s = ~self
            other = -other
        else:
            s = self
        x = self.parent.multiplicative_identity
        for _ in range(other):
            x = x * s
        return x


class Ring:
    elements: frozenset[RingElement]
    additive_identity: RingElement
    addition: Callable[[RingElement, RingElement], RingElement]
    additive_inverse: Callable[[RingElement], RingElement]
    multiplicative_identity: RingElement
    multiplication: Callable[[RingElement, RingElement], RingElement]
    multiplicative_inverse: Optional[Callable[[RingElement], RingElement]]
    name: str

    def __init__(self, elems, a_id, add, a_inv, m_id, mul, m_inv=None, nam="Ring"):
        if not isinstance(next(iter(elems)), RingElement):
            elems = frozenset(RingElement(e, self) for e in elems)
        self.elements = elems
        if not isinstance(a_id, RingElement):
            a_id = RingElement(a_id, self)
        self.additive_identity = a_id
        self.addition = add
        self.additive_inverse = a_inv
        if not isinstance(m_id, RingElement):
            m_id = RingElement(m_id, self)
        self.multiplicative_identity = m_id
        self.multiplication = mul
        self.multiplicative_inverse = m_inv
        self.name = nam

    def __call__(self, obj) -> RingElement:
        elem = RingElement(obj, self)
        assert elem in self.elements
        return elem

    def add(self, a: RingElement, b: RingElement) -> RingElement:
        return RingElement(self.addition(a.value, b.value), self)

    def negate(self, e: RingElement) -> RingElement:
        return RingElement(self.additive_inverse(e.value), self)

    def multiply(self, a: RingElement, b: RingElement) -> RingElement:
        return RingElement(self.multiplication(a.value, b.value), self)

    def reciprocal(self, e: RingElement) -> RingElement:
        assert self.is_field(), "Only fields have multiplicative inverses"
        return RingElement(self.multiplicative_inverse(e.value), self)

    def additive_group(self) -> Group:
        return Group(
            {e.value for e in self.elements},
            self.additive_identity.value,
            self.addition,
            self.additive_inverse,
            "Additive group",
        )

    def multiplicative_group(self) -> Group:
        assert self.is_field(), "Only fields have multiplicative groups"
        return Group(
            {e.value for e in self.elements - frozenset({self.additive_identity})},
            self.multiplicative_identity.value,
            self.multiplication,
            self.multiplicative_inverse,
            "Multiplicative group",
        )

    def order(self) -> int:
        return len(self.elements)

    def is_field(self) -> bool:
        return self.multiplicative_inverse is not None

    def characteristic(self) -> int:
        n = 1
        s = self.multiplicative_identity
        while True:
            if s == self.additive_identity:
                return n
            n += 1
            s += self.multiplicative_identity

    def __str__(self) -> str:
        return f"{self.name} of order {self.order()}"

    def __repr__(self) -> str:
        return str(self)


def matrices(n, ring, known=None, i=1) -> list[Matrix]:
    if known is None:
        known = [Matrix.filled(ring.additive_identity, n, n)]
    new_known = []
    for mat in known:
        for e in ring.elements - frozenset({ring.additive_identity}):
            new_known.append(
                mat.insert(Matrix.filled(e, 1, 1), (i - 1) % n + 1, (i - 1) // n + 1)
            )
    known += new_known
    if i == n**2:
        return known
    else:
        return matrices(n, ring, known, i + 1)


def matrix_ring(n, ring) -> Ring:
    return Ring(
        matrices(n, ring),
        Matrix.filled(ring.additive_identity, n, n),
        Matrix.__add__,
        Matrix.__neg__,
        Matrix.identity(n).map(ring),  # Todo, does not work for non number rings
        Matrix.__matmul__,
    )


def general_linear(n, ring) -> Group:
    return Group(
        [m for m in matrices(n, ring) if m.determinant() != ring.additive_identity],
        Matrix.identity(n).map(ring),
        Matrix.__matmul__,
        Matrix.inverse,
    )


def special_linear(n, ring) -> Group:
    return Group(
        [
            m
            for m in matrices(n, ring)
            if m.determinant() == ring.multiplicative_identity
        ],
        Matrix.identity(n).map(ring),
        Matrix.__matmul__,
        Matrix.inverse,
    )


def projective_general_linear(n, ring) -> Group:
    return Group()


def projective_special_linear(n, ring) -> Group:
    return Group()


def orthogonal_group(n, ring) -> Group:
    return Group(
        [m for m in matrices(n, ring) if m.is_orthogonal()],
        Matrix.identity(n).map(ring),
        Matrix.__matmul__,
        Matrix.inverse,
    )


def special_orthogonal_group(n, ring) -> Group:
    return Group(
        [
            m
            for m in matrices(n, ring)
            if m.is_orthogonal() and m.determinant() == ring.multiplicative_identity
        ],
        Matrix.identity(n).map(ring),
        Matrix.__matmul__,
        Matrix.inverse,
    )


def elliptic_curve(a, b, field):
    if not isinstance(a, RingElement):
        a = field(a)
    if not isinstance(b, RingElement):
        b = field(b)
    inf = (0, float("inf"))
    if 4 * a**3 + 27 * b**2 == field.additive_identity:
        print("Warning: Elliptic curve is singular")

    def add_points(P, Q):
        if P == inf:
            return Q
        if Q == inf:
            return P

        if P[0] == Q[0]:
            if P[1] == -Q[1]:
                return inf
            s = (3 * P[0] ** 2 + a) / (2 * P[1])
            Rx = s**2 - 2 * P[0]
            Ry = P[1] + s * (Rx - P[0])
            return (Rx, -Ry)

        s = (P[1] - Q[1]) / (P[0] - Q[0])
        Rx = s**2 - P[0] - Q[0]
        Ry = P[1] + s * (Rx - P[0])
        return (Rx, -Ry)

    def check(P):
        return P[1] ** 2 == P[0] ** 3 + a * P[0] + b

    points = {(x, y) for x in field.elements for y in field.elements}

    return Group(
        frozenset({P for P in points if check(P)} | {inf}),
        inf,
        add_points,
        lambda P: inf if P == inf else (P[0], -P[1]),
    )


def zero_ring() -> Ring:
    return Ring(
        frozenset({0}),
        0,
        lambda _, __: 0,
        lambda _: 0,
        0,
        lambda _, __: 0,
        lambda _: 0,
        "Zero ring",
    )


def modulo_field(p: int) -> Ring:
    return Ring(
        nset(p),
        0,
        lambda a, b: (a + b) % p,
        lambda a: (-a) % p,
        1,
        lambda a, b: (a * b) % p,
        lambda a: nt.get_inverse_mod(a, p),
        "Galois field",
    )


ZR = zero_ring()

F2 = modulo_field(2)
F3 = modulo_field(3)
F5 = modulo_field(5)
F7 = modulo_field(7)
F11 = modulo_field(11)

GL2_2 = general_linear(2, F2)
GL2_3 = general_linear(2, F3)
