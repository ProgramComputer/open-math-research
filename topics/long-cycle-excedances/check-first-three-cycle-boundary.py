"""Check the transition 3k-1 -> 3k for every k, using the existing two-cycle helpers.

Run with the public topics/long-cycle-excedances directory as the sole argument.
The finite calculation requires python-flint 0.9.0.
"""
from fractions import Fraction as Q
from hashlib import sha256
from math import comb, factorial
from pathlib import Path
from runpy import run_path
from sys import argv


def analytic_constants(topic):
    helper = run_path(str(topic / "verify_two_cycle_bounds.py"))
    tails = helper["tails"]
    mixed = helper["mixed_bounds"]
    q, hi = Q(1, 3), Q(17, 48)
    old_value, old_derivative = tails(Q(1))
    value = max(mixed(Q(j, 48), Q(j + 1, 48))[0] for j in range(16, 24))
    derivative = max(mixed(Q(j, 48), Q(j + 1, 48))[1] for j in range(16, 24))
    lag = 2 * (1 + tails(q)[0]) * (1 + tails(1 - hi)[0]) / (15 * (1 - hi))
    lag += (2 * (1 + tails(q)[0]))**3 / (4 * 65 * 5)
    for weight in (Q(), Q(7, 10)):
        total = (old_value + weight * value)**2 + (old_derivative + weight * derivative + lag)**2
        assert total < (1 + weight)**2
    assert 192 * Q(6, 5) > 15**2
    exp_lower = lambda x: sum(x**j / factorial(j) for j in range(24))
    assert exp_lower(Q(694, 1000)) > 2
    assert Q(694, 1000) + Q(1, 258) < Q(7, 10)
    assert 1 - Q(1, 193) > 0
    assert Q(33, 100) < Q(64, 193)
    assert (1 / (1-Q(1, 12*191)))**2 < Q(7, 8)**2 * 2 * Q(157, 50) * Q(33, 100) * Q(67, 100)
    assert exp_lower(Q(49, 10)) > 130
    assert Q(59, 10)**2 < Q(414, 1000)**2 * Q(157, 50) * 65
    assert (Q(1414, 1000) * Q(777, 80))**2 < 191
    print("First-boundary analytic constants pass for all k >= 65.")


def finite(topic):
    helper = run_path(str(topic / "verify_two_cycle_band.py"))
    eulerian = helper["eulerian_rows"](191)
    base = helper["independent_eulerian_brackets"](eulerian, 126)
    old_row = helper["original_row"]
    signs = helper["Signs"]
    transfer = helper["refine_and_transfer"]
    t = helper["T"]
    digest = sha256()
    pairs, roots = 0, 0
    for k in range(3, 65):
        brackets = base[2*k-2]
        for n in range(2*k-1, 3*k):
            old = old_row(n, k, eulerian)
            if n < 3*k-1:
                actual = old_row(n+1, k, eulerian)
                _, brackets = transfer(signs(old, n-2), (signs(actual, n-1),), brackets, (n,k))
                continue
            # Independent reconstruction by the cycle containing label one.
            actual = eulerian[n]
            for length in range(k, 2*k+1):
                actual += comb(n, length-1) * t * eulerian[length-1] * eulerian[3*k-length-1]
            actual += comb(n, k-1) * comb(2*k-1, k-1) * t**2 * eulerian[k-1]**3
            lag = comb(n, k-1) * eulerian[k-1] * t * old_row(2*k, k, eulerian)
            assert actual == t*(1-t)*old.derivative() + (1+(n-1)*t)*old + lag
            minus = actual - 2*lag
            old_brackets, new_brackets = transfer(
                signs(old, n-2), (signs(actual, n-1), signs(minus, n-1)), brackets, (n,k)
            )
            digest.update(repr((k, old_brackets, new_brackets)).encode("ascii"))
            pairs += 1
            roots += n-2
    assert pairs == 62 and roots == 6045
    print(f"First boundaries k=3..64: {pairs} transitions, {roots} old roots, digest {digest.hexdigest()}.")


if __name__ == "__main__":
    if len(argv) != 2:
        raise SystemExit(__doc__)
    topic = Path(argv[1])
    analytic_constants(topic)
    finite(topic)
