"""Reconstruct the cutoff-seven Lean fixture by exact single- and two-cycle counts."""
from fractions import Fraction
from math import comb
from pathlib import Path
import re


def eulerian(n, j):
    return sum((-1) ** i * comb(n + 1, i) * (j + 1 - i) ** n for i in range(j + 1))


def reduced_count(n, k, j):
    # For k <= n < 3*k, there are at most two cycles. The sum
    # counts each unordered pair twice, also when the lengths coincide.
    two_cycles_twice = sum(
        comb(n, size) * eulerian(size - 1, i) * eulerian(n - size - 1, j - 1 - i)
        for size in range(k, n - k + 1)
        for i in range(j)
    )
    assert two_cycles_twice % 2 == 0
    return eulerian(n - 1, j) + two_cycles_twice // 2


def evaluated(coefficients, modulus):
    result = Fraction(0)
    for coefficient in reversed(coefficients):
        result = coefficient - modulus * result
    return result


def verify():
    lean = Path(__file__).with_name("LongCyclePrefixTail.lean").read_text()
    left, right = Fraction(6, 65536), Fraction(7, 65536)
    for n, signs in ((14, (1, -1)), (15, (-1, -1))):
        pattern = rf"private def quotient{n}Coeff : ℕ → ℕ\n(.*?)  \| _ => 0"
        equations = re.search(pattern, lean, re.S).group(1)
        indexed = [(int(i), int(c)) for i, c in re.findall(r"\| (\d+) => (\d+)", equations)]
        assert indexed == [(j, reduced_count(n, 7, j)) for j in range(n - 1)]
        coefficients = [c for _, c in indexed]
        for endpoint, sign in zip((left, right), signs):
            assert sign * evaluated(coefficients, endpoint) > 0
        print(f"n={n}, k=7: matched {len(coefficients)} exact coefficients and both endpoint signs.")


if __name__ == "__main__":
    verify()
