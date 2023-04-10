from __future__ import annotations
#%%
from cmath import sin, pi, exp
from math import factorial, prod, log
from tools import *


def gamma(z):
    LIMIT_POINT = 50
    num = LIMIT_POINT**z * factorial(LIMIT_POINT)
    den = prod(z+x for x in range(0, LIMIT_POINT+1))
    return num / den


def riemann_zeta(s: complex) -> complex:
    NUM_PARTS = 10000
    if s.real > 1:
        return sum(1/n**s for n in range(1,NUM_PARTS))
    elif s.real < 0:
        return 2**s * pi**(s-1) * sin(pi*s/2) * gamma(1-s) * riemann_zeta(1-s)


class DirichletCharacter:
    m: int
    values: tuple[complex]

    def __init__(self, values):
        self.values = tuple(values)
        self.m = len(self.values)

    def __call__(self, a: int) -> complex:
        return self.values[a%self.m]

    def __mul__(self, other: DirichletCharacter):
        assert self.m == other.m
        return DirichletCharacter(self(a) * other(a) for a in range(0,self.m))

    def conjugate(self):
        return DirichletCharacter(self(a).conjugate() for a in range(0,self.m))

def gauss_sum(chi: DirichletCharacter) -> complex:
    s = 0
    for a in range(1,chi.m+1):
        s += chi(a) * exp(2j * pi * a / chi.m)
    return s



def principal_dirichlet_character(m: int) -> DirichletCharacter:
    return DirichletCharacter(1 if gcd(a,m) == 1 else 0 for a in range(0,m))

def dirichlet_L(s: complex, chi: DirichletCharacter) -> complex:
    NUM_PARTS = 10000
    if s.real > 1:
        return sum(chi(n)/n**s for n in range(1,NUM_PARTS))
    elif s.real < 0:
        a = 0 if chi(-1) == 1 else 1
        eps = gauss_sum(chi) / (1j**a * chi.m**0.5)
        return eps * 2**s * pi**(s-1) * chi.m**(1/2-s) * sin(pi/2 * (s+a)) * gamma(1-s) * dirichlet_L(1 - s, chi.conjugate())

def von_mangoldt(n: int) -> float:
    pf = unique_prime_factors(n)
    if len(pf) == 1:
        return log(next(iter(pf)))
    else:
        return 0

for i in range(1,20):
    print(von_mangoldt(i))
# %%
