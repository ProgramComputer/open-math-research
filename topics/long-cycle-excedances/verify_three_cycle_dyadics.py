"""Independent cycle coefficients and integer-only dyadic exterior signs."""
from argparse import ArgumentParser
from fractions import Fraction
from functools import lru_cache
from math import comb
from pathlib import Path
from runpy import run_path

from flint import fmpz_poly

HERE = Path(__file__).resolve().parent
sign_at_negative_dyadic = run_path(str(HERE / "three_cycle_dyadic_sign.py"))["sign_at_negative_dyadic"]
eulerian_prefixes = run_path(str(HERE / "three_cycle_prefix.py"))["eulerian_prefixes"]


WIDTH = 48
BITS = 128
T = fmpz_poly([0, 1])
SAMPLES = (
    (192, 49), (192, 55), (192, 64), (195, 49),
    (255, 64), (256, 73), (257, 86),
    (383, 96), (384, 110), (385, 128),
    (511, 128), (512, 146), (513, 171),
    (767, 192), (768, 220), (769, 256),
    (1023, 256), (1024, 293), (1025, 342),
    (1535, 384), (1536, 439), (1537, 512),
    (2047, 512), (2048, 585), (2049, 683),
    (2198, 733), (2199, 550), (2199, 628), (2199, 733),
)


class Endpoints:
    def __init__(self):
        self.rows = []

    def update(self, line):
        self.rows.append(tuple(int(item) for item in line.split(b',')))


def cycle_choices(size, first, last):
    if first > last:
        return
    coefficient = comb(size-1, first-1)
    for length in range(first, last+1):
        yield length, coefficient
        coefficient = coefficient * (size-length) // length


def independent_rows(n, k, euler):
    """Construct by the length of the cycle containing the minimum label."""
    empty = fmpz_poly()

    @lru_cache(None)
    def two(size):
        result = empty
        if size < 2*k:
            return result
        choice = comb(size, k)
        for length in range(k, size//2+1):
            product = euler[length-1].mul_low(euler[size-length-1], WIDTH-1)
            multiplicity = choice//2 if 2*length == size else choice
            result += multiplicity*product
            choice = choice * (size-length) // (length+1)
        return result

    def row(size):
        result = euler[size-1] + T*two(size)
        three = empty
        for length, choice in cycle_choices(size, k, size-2*k):
            product = euler[length-1].mul_low(two(size-length), WIDTH-2)
            three += choice*product
        result += T**2*three
        if size == 4*k:
            base = euler[k-1]
            square = base.mul_low(base, WIDTH-3)
            scalar = comb(4*k,k)*comb(3*k,k)*comb(2*k,k)//24
            result += scalar*T**3*square.mul_low(square, WIDTH-3)
        return result

    old = row(n)
    positive = row(n+1)
    lag = comb(n,k-1)*T*euler[k-1].mul_low(row(n+1-k), WIDTH-1)
    return old, positive, positive-2*lag


def check_eulerian_prefix(index, row):
    for degree in range(min(index, WIDTH)):
        expected = sum(
            (-1)**j * comb(index+1, j) * (degree+1-j)**index
            for j in range(degree+1)
        )
        if row[degree] != expected:
            raise ArithmeticError((index, degree, "Eulerian coefficient"))


def lower_dyadic(value):
    mantissa, exponent = map(int, value.lower().man_exp())
    if mantissa <= 0:
        raise ArithmeticError("Expected a positive lower endpoint")
    trim = max(0, mantissa.bit_length()-96)
    numerator, denominator_bits = mantissa >> trim, -(exponent+trim)
    if denominator_bits <= 0:
        raise ArithmeticError("Expected modulus below one")
    return numerator, denominator_bits


@lru_cache(maxsize=None)
def omitted_powers(n):
    return (WIDTH+1)**n, (WIDTH+2)**n


def integer_sign(poly, n, numerator, bits):
    if numerator == 0:
        return (poly[0] > 0) - (poly[0] < 0)
    if numerator.bit_length() >= bits:
        raise ArithmeticError("Expected modulus below one")
    value = 0
    for coefficient in reversed(poly):
        value = (coefficient << BITS) - ((numerator * value) >> bits)
    # One floor error per stage gives scaled error strictly below WIDTH.
    a = bits-numerator.bit_length()
    first, second = omitted_powers(n)
    if a >= 1 and (first << (a-1)) >= second:
        exponent = 1+BITS-WIDTH*a
        if exponent >= 0:
            tail = first << exponent
        else:
            divisor = 1 << -exponent
            tail = (first + divisor - 1)//divisor
        if abs(value) > WIDTH+tail:
            return (value > 0)-(value < 0)
    return sign_at_negative_dyadic(poly, n, WIDTH, numerator, bits)


def greater(a, b):
    return (a[0] << b[1]) > (b[0] << a[1])


def audit(n,k,reference,euler):
    width, grid = reference["KEEP"], reference["GRID"]
    if width != WIDTH:
        raise ArithmeticError("Reference certifier prefix width changed")
    modulus = reference["modulus"]
    for index in {k-1, n-k, n-1, n}:
        check_eulerian_prefix(index, euler[index])
    coefficients = independent_rows(n,k,euler)
    # Use the existing phase search only to propose dyadic audit endpoints.
    endpoints = Endpoints()
    reference["check_exterior"](n,k,*(T*row for row in coefficients),endpoints)
    polys = [tuple(int(row[j]) for j in range(WIDTH)) for row in coefficients]
    previous = (0,0)
    for expected_rank, (size, cap, rank, left, right) in enumerate(endpoints.rows,1):
        if (size,cap,rank) != (n,k,expected_rank) or not 0<left<right<=20*grid:
            raise ArithmeticError((n,k,rank,"invalid recorded phase bracket"))
        lo = lower_dyadic(modulus(n,left))
        hi = lower_dyadic(modulus(n,right))
        if not greater(lo,previous) or not greater(hi,lo):
            raise ArithmeticError((n,k,rank,"dyadic order"))
        goal = (-1)**rank
        actual = [integer_sign(poly, next_size, *end)
                  for end in (lo,hi) for poly,next_size in zip(polys,(n,n+1,n+1))]
        if actual != [-goal,goal,goal,goal,goal,goal]:
            raise ArithmeticError((n,k,rank,actual))
        previous=hi
    if len(endpoints.rows) != 19:
        raise ArithmeticError((n,k,"wrong rank count"))
    middle = modulus(n,20*grid).lower()
    mant, exponent = map(int,middle.man_exp())
    exact_middle_lower = Fraction(mant, 1 << -exponent) if exponent < 0 else Fraction(mant << exponent)
    if Fraction(previous[0], 1 << previous[1]) > exact_middle_lower:
        raise ArithmeticError((n,k,"dyadic exterior-middle join"))
    return 19


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("reference", type=Path)
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--stop", type=int, default=len(SAMPLES))
    args = parser.parse_args()
    samples = SAMPLES[args.start:args.stop]
    euler = eulerian_prefixes(max(n for n,_ in samples), WIDTH)
    reference = run_path(str(args.reference))
    reference["check_middle_join"]()
    count=0
    for n,k in samples:
        if not 192 <= n < 2200 or not 3*k-1<=n<4*k:
            raise ArithmeticError((n,k,"sample outside three-cycle band"))
        count+=audit(n,k,reference,euler)
        print(f'{n},{k}: 19 certified dyadic brackets; {count} cumulative',flush=True)
    print(f'Audited {count} brackets and {6*count} polynomial signs on {len(samples)} pairs.')


if __name__ == '__main__':
    main()
