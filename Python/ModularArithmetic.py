import math_utils.NumberTheory.tools as nt
import math
import random

print(nt.get_inverse_mod(3, 7))

def number_to_base(n, b):
    if n == 0:
        return [0]
    digits = []
    while n:
        digits.append(int(n % b))
        n //= b
    return digits[::-1]

def play():
    print("Modular Arithmetic\n")
    serial = [random.randint(0,9) for _ in range(3)]
    print(f"Serial digits are {serial}\n")

    DS = sum(serial)

    while True:
        p1, p2, p3 = random.sample([2,3,5,7,11], 3)
        if p3 != 2:
            break

    # p1 - exponent
    print(f"First prime is {p1}")
    # p2 - inverse
    print(f"Second prime is {p2}")
    # p3 - reciprocity
    print(f"Third prime is {p3}\n")

    while True:
        flashes = random.randint(6, 20)
        if nt.are_coprime(flashes, p1) and nt.are_coprime(flashes, p2):
            break
    
    print(f"The lights are flashing {flashes} times")

    a1 = nt.pow_mod(flashes, DS, p1)

    a2 = nt.get_inverse_mod(flashes, p2)

    a3 = (flashes + DS + nt.legendre_symbol(flashes + DS, p3)) % p3

    # HIDDEN
    print(a1, a2, a3)

    x = nt.chinese_remainder((a1,p1),(a2,p2),(a3,p3))

    # HIDDEN
    print(x)

    seq = number_to_base(x, 3)

    # HIDDEN
    print(seq)

    for d in seq:
        print("What is the next button to press (0,1,2)?")
        i = input("> ")
        if i not in ("0", "1", "2") or int(i) != d:
            break
    else:
        print("Disarmed")
        return

    print("Exploded")

if __name__ == "__main__":
    play()