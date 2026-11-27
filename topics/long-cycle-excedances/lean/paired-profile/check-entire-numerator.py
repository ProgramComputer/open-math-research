"""Reconstruct both sides of the cleared cycle identity through degree nine."""
from fractions import Fraction
from itertools import permutations
from math import factorial

DEGREE = 9


def minimum_cycle_length(permutation):
    unseen = set(range(len(permutation)))
    minimum = len(permutation) + 1
    while unseen:
        current = next(iter(unseen))
        length = 0
        while current in unseen:
            unseen.remove(current)
            current = permutation[current]
            length += 1
        minimum = min(minimum, length)
    return minimum


def exclusion_exponential(cutoff):
    coefficients = [Fraction(1)] + [Fraction(0)] * DEGREE
    for length in range(1, cutoff):
        new = [Fraction(0)] * (DEGREE + 1)
        for n, coefficient in enumerate(coefficients):
            for count in range((DEGREE - n) // length + 1):
                weight = Fraction((-1) ** count, length**count * factorial(count))
                new[n + count * length] += coefficient * weight
        coefficients = new
    coefficients[0] -= 1
    coefficients[1] += 1
    return coefficients


def main():
    cutoffs = range(2, DEGREE + 2)
    counts = {k: [1] + [0] * DEGREE for k in cutoffs}
    for n in range(1, DEGREE + 1):
        histogram = [0] * (n + 1)
        for permutation in permutations(range(n)):
            histogram[minimum_cycle_length(permutation)] += 1
        for k in cutoffs:
            counts[k][n] = sum(histogram[k:])
    for k in cutoffs:
        nonempty = [Fraction(0)] + [Fraction(counts[k][n], factorial(n))
                                   for n in range(1, DEGREE + 1)]
        numerator = [nonempty[0]] + [nonempty[n] - nonempty[n - 1]
                                    for n in range(1, DEGREE + 1)]
        if numerator != exclusion_exponential(k):
            raise ArithmeticError(f"coefficient mismatch at cutoff {k}")
        print("k", k, "coefficients", *numerator)
    print("PASS: 90 exact coefficients from all permutations through size nine")


if __name__ == "__main__":
    main()
