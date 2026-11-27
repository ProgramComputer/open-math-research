"""Exact signed remainder chains for the first pair and the analytic cutoff seam."""
from itertools import permutations
from math import comb
from flint import fmpz_poly

K = 7
X = fmpz_poly([0, 1])


def original_rows(limit):
    """Cycle containing label 1. Each m-cycle contributes t*A_(m-1)."""
    eulerian = [fmpz_poly([1])]
    rows = [fmpz_poly([1])]
    for n in range(1, limit + 1):
        previous = eulerian[n-1]
        eulerian.append((1+(n-1)*X)*previous + X*(1-X)*previous.derivative())
        row = sum((comb(n-1, m-1) * X * eulerian[m-1] * rows[n-m]
                   for m in range(K, n+1)), fmpz_poly([]))
        rows.append(row)
    return rows


def literal(n):
    row = [0]*(n+1)
    for perm in permutations(range(n)):
        unseen = set(range(n))
        allowed = True
        while unseen:
            i = min(unseen)
            length = 0
            while i in unseen:
                unseen.remove(i)
                length += 1
                i = perm[i]
            if length < K:
                allowed = False
                break
        if allowed:
            row[sum(i < j for i,j in enumerate(perm))] += 1
    return fmpz_poly(row)


def interlace(new, old):
    count = 0
    while old.degree():
        assert new.degree() == old.degree()+1 and old.leading_coefficient() > 0
        remainder = new
        while remainder.degree() >= old.degree():
            shift = remainder.degree()-old.degree()
            remainder = (old.leading_coefficient()*remainder -
                         remainder.leading_coefficient()*old.left_shift(shift))
        assert remainder.degree() == old.degree()-1 and remainder.leading_coefficient() < 0
        new, old = old, (-remainder) // remainder.content()
        count += 1
    assert new.degree() == 1 and old.degree() == 0 and old[0] > 0
    return count


if __name__ == "__main__":
    rows = original_rows(96)
    for n in [7, 8]:
        assert rows[n] == literal(n)
    for n in [7, 94, 95]:
        old, new = rows[n], rows[n+1]
        assert (old[0], old[1], new[0], new[1]) == (0, 1, 0, 1)
        assert all(c >= 0 for p in [old,new] for c in p)
        assert old.degree() == n-1 and new.degree() == n
        steps = interlace(new // X, old // X)
        print(f"lower={n} upper={n+1} quotient degrees={n-2},{n-1} signed remainders={steps}")
