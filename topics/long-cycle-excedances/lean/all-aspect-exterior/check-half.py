"""Exact near-half-cutoff checks using the single-cycle and two-cycle decomposition."""
from functools import cache
from itertools import permutations
from math import comb, isqrt
from hashlib import sha256


@cache
def eulerian(m, j):
    if not 0 <= j < max(m, 1):
        return 0
    return sum((-1)**i * comb(m+1, i) * (j+1-i)**m for i in range(j+1))


def product_coeff(a, b, p):
    return sum(eulerian(a-1, i-1)*eulerian(b-1, p-i-1) for i in range(1, p))


def coefficient(n, k, p):
    assert 0 < n < 3*k
    if n < k:
        return 0
    ordered = sum(comb(n, a)*product_coeff(a, n-a, p) for a in range(k, n-k+1))
    assert ordered % 2 == 0
    return eulerian(n-1, p-1) + ordered//2


def literal(n, k):
    ans = [0]*(n+1)
    for pi in permutations(range(n)):
        seen = set()
        for start in range(n):
            if start in seen:
                continue
            j, length = start, 0
            while j not in seen:
                seen.add(j)
                j, length = pi[j], length+1
            if length < k:
                break
        else:
            ans[sum(j > i for i,j in enumerate(pi))] += 1
    return ans


def verify(n, k, rank):
    assert n+1 < 3*k and n >= 10000 and rank == isqrt(n)//2 and n >= k >= 2
    previous = 0
    out = sha256()
    words = [0,0,0]
    for p in range(1, rank+1):
        old = coefficient(n, k, p)
        new = coefficient(n+1, k, p)
        m = n+1-k
        lag = comb(n, k-1)*product_coeff(k, m, p) if m >= k else 0
        assert lag == new-p*old-(n-p+1)*previous
        assert 25*lag < 8*old and lag >= 0
        assert 297*n*p**n <= 100*(3*n + 8*k*p)*old
        assert 0 < old <= p**n and 100*k*p*old <= 151*n*p**n
        for j, value in enumerate([old, new, lag]):
            buf = value.to_bytes((value.bit_length()+7)//8, 'big')
            out.update(len(buf).to_bytes(8,'big')+buf)
            words[j] += value > 0
        previous = old
    print(n,k,rank,words,out.hexdigest(),flush=True)


if __name__ == '__main__':
    small = 0
    for n in range(1, 9):
        for k in range(2, n+2):
            if n < 3*k:
                assert [coefficient(n,k,j) for j in range(n+1)] == literal(n,k)
                small += 1
    print(small, 'complete rows matched literal permutations',flush=True)
    for n, k in [(10000,5000),(10001,5001),(10000,5002),(10008,5000)]:
        verify(n,k,isqrt(n)//2)
