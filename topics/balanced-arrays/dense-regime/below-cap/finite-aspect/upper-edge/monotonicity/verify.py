"""Two independent counts of the row-slack excess for rank-two arrays."""
from fractions import Fraction
from math import comb
from runpy import run_path
from pathlib import Path


def histogram_excess(n, d, k):
    """Track the number of double rows while exposing the labeled columns."""
    counts = [1]
    for col in range(d):
        used = col * k
        next_counts = [0] * ((used + k) // 2 + 1)
        for doubles, count in enumerate(counts):
            singles = used - 2 * doubles
            empty = n - used + doubles
            if count == 0:
                continue
            for j in range(max(0, k - empty), min(k, singles) + 1):
                next_counts[doubles+j] += count * comb(singles,j) * comb(empty,k-j)
        counts = next_counts

    slack = 2*n - d*k
    active_sum = sum((n-h)*count for h,count in enumerate(counts))
    return Fraction(active_sum, sum(counts)) - Fraction(n*slack, n+slack-1)


def main():
    matching_excess = run_path(str(Path(__file__).with_name("matching.py")))["error"]
    n, d = 8600, 80
    lower, higher = (histogram_excess(n,d,k)/n for k in (15,16))
    assert lower == matching_excess(n,(15,)*d)/n
    assert higher == matching_excess(n,(16,)*d)/n
    assert Fraction(341042,10**6) < lower < Fraction(341043,10**6)
    assert Fraction(341077,10**6) < higher < Fraction(341078,10**6)
    larger_slack = 2*n-15*d
    assert Fraction(larger_slack**2*d,n*n*2*(d-2)) == Fraction(128000,72111) < Fraction(16,9)
    print("The column histogram and multipartite matching counts agree at k=15 and k=16.")
    print("E(16000)/n lies in (0.341042, 0.341043), E(15920)/n in (0.341077, 0.341078).")
    print("The squared larger normalized slack is 128000/72111 < 16/9.")


if __name__ == "__main__":
    main()
