# %%
from math import isqrt, prod
from typing import Iterator
from time import perf_counter
from collections import Counter

def list_sublists(l: list) -> list[list]:
    if len(l) == 0:
        return [[]]

    l_copy = l.copy()
    e = l_copy.pop()
    l_copy_sublists = list_sublists(l_copy)
    return l_copy_sublists + [[e] + l_copy_sublist for l_copy_sublist in l_copy_sublists]

    
def sgn(n: int) -> int:
    if n == 0:
        return 0
    return n // abs(n)

def prime_factors(n: int) -> list[int]:
    if n == 1:
        return []
    pfs = []
    for p in gen_primes():
        while n % p == 0:
            pfs.append(p)
            n //= p
        if n == 1:
            break
    return pfs

def unique_prime_factors(n: int) -> set[int]:
    return set(prime_factors(n))

def prime_factorisation(n: int) -> Counter:
    return Counter(prime_factors(n))

def prime_signature(n: int) -> Counter:
    return Counter(prime_factorisation(n).values())

def divisors(n: int) -> set[int]:
    return set(prod(l) for l in list_sublists(prime_factors(n)))

def proper_divisors(n: int) -> set[int]:
    return divisors(n) - {n}
    
def nondivisors(n: int) -> set[int]:
    return {i for i in range(1, n)} - divisors(n)

def sum_divisors(n: int, z: complex = 1) -> complex:
    return sum(d ** z for d in divisors(n))

def aliquot_sum(n: int) -> int:
    return sum(proper_divisors(n))

def is_perfect(n: int) -> bool:
    return n == aliquot_sum(n)

def aliquot_sequence(n: int) -> Iterator:
    while True:
        yield n
        n = aliquot_sum(n)

def is_powerful(n: int) -> bool:
    for a in prime_signature(n):
        if a < 2:
            return False
    return True

def is_prime(n: int) -> bool:
    isq = isqrt(n)
    for p in dynamic_sieve():
        if p > isq:
            break
        if n % p == 0:
            return False
    return True

def gen_primes() -> Iterator[int]:
    yield 2
    yield 3
    yield 5
    yield 7
    primes = [5,7]
    i = 11
    step = 2
    while True:
        isq = isqrt(i)
        for p in primes:
            if p > isq:
                primes.append(i)
                yield i
                break
            if i % p == 0:
                break
        i += step
        step = 2 if step == 4 else 4

def dynamic_sieve() -> Iterator[int]:
    size = 64
    prime = [True] * size
    prime[0] = False
    prime[1] = False
    start = 2
    hitters = []
    while True:
        for i in range(start, size):
            if prime[i]:
                yield i
                j = i
                for j in range(i * 2, size, i):
                    prime[j] = False
                hitters.append([j, i])
        extension = [True] * size
        prime.extend(extension)
        start = size
        size *= 2
        for hitter in hitters:
            pos, step = hitter
            for j in range(pos + step, size, step):
                prime[j] = False
            hitter[0] = j


def sieve(size: int) -> list[bool]:
    prime = [True] * size
    prime[0] = False
    prime[1] = False
    for i in range(2, size):
        if prime[i]:
            for j in range(i * 2, size, i):
                prime[j] = False
    return prime

def list_primes(size: int) -> list[int]:
    prime_sieve = sieve(size)
    return [i for i in range(size) if prime_sieve[i]]

def prime_count(n: int) -> int:
    pi = 0
    primes = dynamic_sieve()
    while next(primes) <= n:
        pi += 1
    return pi

def gcd(n: int, m: int) -> int:
    if 0 in {n,m}:
        return max(n, m)
    return gcd(m, n % m)

def lcm(n: int, m: int) -> int:
    return n * m // gcd(n,m) 

def are_coprime(n: int, m: int) -> bool:
    return gcd(n, m) == 1
    
def coprimes(n: int) -> set[int]:
    return {i for i in range(1, n) if gcd(i, n) == 1}

def bezout(n: int, m: int) -> tuple[int, int, int]:
    if n == 0:
        return (m, 0, 1)
    elif m == 0:
        return (n, 1, 0)
    g, s, t = bezout(m, n % m)
    return (g, t, s - n // m * t)

def chinese_remainder(*congruences : tuple[int, int]):
    N = prod(congruence[1] for congruence in congruences)
    X = 0
    for a, n in congruences:
        rest = N // n
        _, _, t = bezout(n, rest)
        A = t * rest
        X += a * A
    return X % N

def get_inverse_mod(a: int, n: int) -> int:
    triplet = bezout(a, n)
    assert triplet[0] == 1, 'Only numbers that are coprime with n have inverses mod n'
    return triplet[1] % n

def pow_mod(a: int, b: int, n: int) -> int:
    prod = 1
    k = a % n
    for bit in bin(b)[2:][::-1]:
        if bit == '1':
            prod = prod * k % n
        k = k**2 % n
    return prod

def euler_totient(n: int) -> int:
    phi = 1
    for prime, power in prime_factorisation(n).items():
        phi *= (prime-1) * prime**(power-1)
    return phi

def jordan_totient(k:int, n: int) -> int:
    phi = 1
    for prime, power in prime_factorisation(n).items():
        phi *= (prime-1) * prime**(power-1)
    return phi

def is_squarefree(n: int) -> bool:
    pfs = prime_factors(n)
    return len(pfs) == len(set(pfs))

def liouville(n: int) -> int:
    return (-1)**len(prime_factors(n))

def mobius(n: int) -> int:
    return liouville(n) if is_squarefree(n) else 0

def legendre_symbol(a: int, p: int) -> int:
    return ((a ** ((p-1)//2)) + 1) % p - 1

def legendre_sequence(p: int) -> Iterator[int]:
    a = 0
    while True:
        yield legendre_symbol(a, p)
        a += 1

def jacobi_symbol(a: int, n: int) -> int:
    pf = prime_factorisation(n)
    jacobi = 1
    for p in pf:
        jacobi *= legendre_symbol(a, p) ** pf[p]
    return jacobi

def kronecker_symbol(a: int, n: int) -> int:
    if n == 0:
        if abs(a) == 1:
            return 1
        else:
            return 0
    u = sgn(n)
    pf = prime_factorisation(abs(n))
    kronecker = 1 if u == 1 else (-1 if a < 0 else 1)
    for p in pf:
        if p == 2:
            if a % 2 == 0:
                jacobi = 0
            elif a % 8 in [1,7]:
                jacobi = 1
            else:
                jacobi = -1
        else:
            jacobi = legendre_symbol(a,p)
        kronecker *= jacobi ** pf[p]
    return kronecker
    
def is_pseudoprime(n: int, a: int):
    return pow_mod(a, n - 1, n) == 1
    
def is_carmichael(n: int):
    if is_prime(n):
        return False
    for b in coprimes(n):
        if not is_pseudoprime(n, b):
            print(b)
            return False
    return True
    
def is_strong_pseudoprime(n: int, a: int):
    twos = 0
    q = n - 1
    while q % 2 == 0:
        twos += 1
        q //= 2
    if pow_mod(a, q, n) == 1:
        return True
    for pow in range(0, twos):
        if pow_mod(a, 2**pow * q, n) == n - 1:
            return True
    return False
if __name__ == "__main__":
    from time import perf_counter
    t = perf_counter()
    for p in dynamic_sieve():
        if p > 5_000:
            break
    print(perf_counter()-t)
# %%
