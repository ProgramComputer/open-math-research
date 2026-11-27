"""Low coefficients via exclusion of short cycles in the exponential generating series."""
from functools import cache
from itertools import permutations
from math import comb
from hashlib import sha256
import argparse


@cache
def eulerian(n):
    if n == 0:
        return (1,)
    prev = (0, *eulerian(n - 1), 0)
    return tuple((i + 1) * prev[i + 1] + (n - i) * prev[i] for i in range(n))


def labeled_rows(k, rank, base):
    # rows[m][l] is l! times the coefficient of t^m z^l in exp(G).
    # Distinguish one label and choose the rest of its block from the other labels.
    blocks = [(1, 1, -base - 1)]
    for j in range(2, k):
        blocks.extend((j, s, -v) for s, v in enumerate(eulerian(j - 1), 1) if s <= rank)
    rows = [[1]]
    for m in range(1, rank + 1):
        row = [0] * ((k - 1) * m + 1)
        for j, s, weight in blocks:
            if s > m:
                continue
            for r, value in enumerate(rows[m - s]):
                if value:
                    row[r + j] += comb(r + j - 1, j - 1) * weight * value
        rows.append(row)
    return rows


def prefix(n, k, rank):
    out = [0] * (rank + 1)
    for base in range(rank + 1):
        rows = labeled_rows(k, rank - base, base)
        max_degree = min(n, (rank - base) * (k - 1))
        # Binomial Taylor coefficients of the remaining exponential in the EGF.
        c = [comb(n, l) for l in range(max_degree + 1)]
        for m, row in enumerate(rows):
            last = min(n, len(row) - 1)
            if base == 0 and last < n:
                continue
            prev = rows[m - 1] if m else ()
            v = 0
            for l in range(last + 1):
                v = v * base + c[l] * (row[l] - (prev[l] if l < len(prev) else 0))
            out[base + m] += v * pow(base, n - last)
    return out


def literal(n, k):
    coeff = [0] * (n + 1)
    for perm in permutations(range(n)):
        seen = set()
        for i in range(n):
            if i in seen:
                continue
            length, j = 0, i
            while j not in seen:
                seen.add(j)
                j = perm[j]
                length += 1
            if length < k:
                break
        else:
            coeff[sum(j > i for i, j in enumerate(perm))] += 1
    return coeff


def check_rank(n, k, rank):
    a = prefix(n, k, rank)
    residual = prefix(n + 1 - k, k, rank - 1)
    b = eulerian(k - 1)
    lag = []
    choices = comb(n, k - 1)
    for j in range(rank + 1):
        convolution = sum(b[i] * residual[j - 1 - i] for i in range(min(j, len(b))))
        lag.append(choices * convolution)
    successor = prefix(n + 1, k, rank)
    for j in range(1, rank + 1):
        assert successor[j] == j*a[j] + (n-j+1)*a[j-1] + lag[j]
    assert a[0] == lag[0] == 0 and a[1] == 1
    for j in range(1, rank + 1):
        # Check the literal alpha envelopes and the original lag, using integers.
        assert 4*j*j <= n and n > 4000*k and 2 <= k and 10000 <= n
        power = pow(j, n)
        assert 297*n*power <= 100*(3*n + 8*k*j)*a[j]
        assert a[j] <= power and 100*k*j*a[j] <= 151*n*power
        assert 0 <= 8*lag[j] < a[j]
    def digest(nums):
        h = sha256()
        for c in nums:
            data = c.to_bytes((c.bit_length() + 7)//8, 'big')
            h.update(len(data).to_bytes(8, 'big'))
            h.update(data)
        return h.hexdigest()
    return digest(a), digest(lag)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--case', nargs=3, type=int, action='append', default=[])
    parser.add_argument('--literal', action='store_true')
    a = parser.parse_args()
    if a.literal:
        pairs = 0
        for n in range(9):
            for k in range(2, max(n + 2, 4)):
                assert prefix(n, k, n) == literal(n, k), (n, k)
                pairs += 1
        print(f'{pairs} complete rows agree with literal permutation enumeration.', flush=True)
    for n, k, rank in a.case:
        if k < 2 or n < 10_000 or n <= 4000*k or rank < 1 or 4*rank**2 > n:
            parser.error('each case requires k≥2, n≥10000, n>4000k, rank≥1 and 4 rank²≤n')
        d1, d2 = check_rank(n, k, rank)
        print(n, k, rank, d1, d2, flush=True)
