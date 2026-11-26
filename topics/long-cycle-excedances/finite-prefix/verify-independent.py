"""Independent partition vectors and exact Sturm checks in the original variable."""
from collections import Counter, defaultdict
from contextlib import redirect_stdout
from fractions import Fraction
from functools import lru_cache
from io import StringIO
from itertools import permutations
from math import comb, factorial, gcd
from pathlib import Path
import re
import runpy

from flint import fmpz_poly

ROOT = Path(__file__).resolve().parent
T = fmpz_poly([0, 1])
ONE_PLUS_T = fmpz_poly([1, 1])
LOW_PAIRS = ((16, 4), (17, 4), (20, 4), (20, 5), (21, 5), (24, 6),
             (25, 6), (27, 4), (31, 6), (32, 4))
HIGH_PAIRS = ((96, 24), (101, 19), (149, 37), (167, 40), (200, 50),
              (231, 51), (234, 42), (248, 62), (249, 62), (250, 42), (250, 62))


@lru_cache(None)
def finite_difference_eulerian(r):
    """A_r coefficients by inclusion–exclusion on descents."""
    left = [
        sum((-1)**i * comb(r + 1, i) * (j + 1 - i)**r for i in range(j + 1))
        for j in range((r + 1)//2)
    ]
    right = left[:-1] if r % 2 else left
    return fmpz_poly(left + right[::-1])


def sorted_partitions(size, minimum):
    if size < minimum:
        return
    yield (size,)
    for first in range(minimum, size//2 + 1):
        for tail in sorted_partitions(size - first, first):
            yield (first, *tail)


@lru_cache(None)
def by_cycle_partitions(n, k):
    """Ordinary indexed coefficients of Q=E/t, with no coefficient recurrence."""
    result = fmpz_poly()
    for parts in sorted_partitions(n, k):
        weights = Counter(parts)
        divisor = 1
        product = T**(len(parts)-1)
        for length, repeats in weights.items():
            divisor *= factorial(length)**repeats * factorial(repeats)
            product *= finite_difference_eulerian(length-1)**repeats
        quotient, remainder = divmod(factorial(n), divisor)
        assert not remainder
        result += quotient * product
    return tuple(int(c) for c in result)


def brute_excedances():
    """Enumerate actual permutation cycles and excedances for n through eight."""
    total = 0
    for n in range(3,9):
        outcomes = defaultdict(Counter)
        for perm in permutations(range(n)):
            unseen = set(range(n))
            shortest = n
            while unseen:
                start = min(unseen)
                j = start
                length = 0
                while j in unseen:
                    unseen.remove(j)
                    j = perm[j]
                    length += 1
                assert j == start
                shortest = min(shortest, length)
            if shortest >= 3:
                excedances = sum(i < v for i,v in enumerate(perm))
                for k in range(3, shortest + 1):
                    outcomes[k][excedances-1] += 1
        for k in range(3,n+1):
            assert tuple(outcomes[k][j] for j in range(n-1)) == by_cycle_partitions(n,k)
            total += 1
    return total


def certify_script_rows():
    samples = defaultdict(set)
    for n,k in (*LOW_PAIRS, *HIGH_PAIRS):
        samples[k].update((n, n+1))
    # Compare the actual vector handed into the certifier, before root checking.
    fn = runpy.run_path(str(ROOT / 'certify.py'))['certify']
    original = fn.__globals__['Signs']
    total = 0
    for k,sizes in sorted(samples.items()):
        recorded = set()

        class Capture(original):
            def __init__(self, gamma, n):
                if n in sizes:
                    lift = sum((int(c)*T**j*ONE_PLUS_T**(n-2-2*j)
                                for j,c in enumerate(gamma)), fmpz_poly())
                    assert tuple(int(c) for c in lift) == by_cycle_partitions(n,k), (n,k)
                    recorded.add(n)
                super().__init__(gamma,n)

        fn.__globals__['Signs'] = Capture
        with redirect_stdout(StringIO()):
            fn(max(sizes)-1, [k], k, k)
        assert recorded == sizes
        total += len(recorded)
    fn.__globals__['Signs'] = original
    return total


def sign(value):
    return (value > 0) - (value < 0)


def positive_primitive(coeffs):
    while coeffs and coeffs[-1] == 0:
        coeffs.pop()
    if not coeffs:
        return coeffs
    d = gcd(*coeffs)
    return [c//d for c in coeffs]


def positive_scaled_remainder(a, b):
    """Return a positive rational multiple of the exact rational remainder."""
    a = list(a)
    lead = b[-1]
    while len(a) >= len(b):
        offset = len(a)-len(b)
        cross = sign(lead)*a[-1]
        a = [abs(lead)*c for c in a]
        for j,c in enumerate(b):
            a[offset+j] -= cross*c
        a = positive_primitive(a)
    return a


def sturm(polynomial):
    seq = [list(polynomial), [j*c for j,c in enumerate(polynomial) if j]]
    while len(seq[-1]) > 1:
        nxt = positive_scaled_remainder(seq[-2], seq[-1])
        assert nxt, 'multiple roots in a sampled row'
        seq.append([-c for c in nxt])
    return seq


def polynomial_sign(coeffs, x):
    numerator, denominator = x.numerator, x.denominator
    top = coeffs[-1]
    scale = denominator
    for coefficient in reversed(coeffs[:-1]):
        top = top*numerator + coefficient*scale
        scale *= denominator
    return sign(top)


def variations(values):
    nz = [v for v in values if v]
    return sum(a != b for a,b in zip(nz,nz[1:]))


def at(psturm, point):
    return variations(polynomial_sign(poly,point) for poly in psturm)


def infinity(psturm):
    return variations(sign(poly[-1]) for poly in psturm)


def direct_interlacing(n,k):
    """Isolate old and next roots of Q(-y) in positive y without gamma coordinates."""
    polynomials = [
        [(-1)**j*c for j,c in enumerate(by_cycle_partitions(row,k))]
        for row in (n,n+1)
    ]
    sequences = [sturm(poly) for poly in polynomials]
    base = [at(seq,Fraction(0)) for seq in sequences]
    final = [infinity(seq) for seq in sequences]
    assert [b-f for b,f in zip(base,final)] == [n-2,n-1]
    upper = Fraction(1)
    for _ in range(1024):
        if all(polynomial_sign(poly,upper) for poly in polynomials):
            if [at(seq,upper) for seq in sequences] == final:
                break
        upper *= 2
    else:
        raise ArithmeticError('upper endpoint unresolved')

    stack = [(Fraction(0),upper,base,final,0)]
    intervals = []
    while stack:
        left,right,v_left,v_right,depth = stack.pop()
        counts = [a-b for a,b in zip(v_left,v_right)]
        assert all(c >= 0 for c in counts)
        if not sum(counts):
            continue
        if sum(counts)==1:
            intervals.append((left,right,counts.index(1)))
            continue
        assert depth < 1024, 'joint Sturm intervals did not separate'
        point = (left+right)/2
        for _ in range(1024):
            if all(polynomial_sign(poly,point) for poly in polynomials):
                break
            point = (left+point)/2
        else:
            raise ArithmeticError('midpoint exactly on too many roots')
        middle = [at(seq,point) for seq in sequences]
        stack.append((point,right,middle,v_right,depth+1))
        stack.append((left,point,v_left,middle,depth+1))

    assert [owner for _,_,owner in intervals] == [1,0]*(n-2)+[1]
    for rank,(left,right) in enumerate(
        ((a,b) for a,b,owner in intervals if owner==0), start=1
    ):
        assert polynomial_sign(polynomials[0],left) == (-1)**(rank-1)
        assert polynomial_sign(polynomials[0],right) == (-1)**rank
        assert polynomial_sign(polynomials[1],left) == polynomial_sign(
            polynomials[1],right
        ) == (-1)**rank
    return len(intervals)


def inspect_logs():
    counters = {}
    line_re = re.compile(
        r'^k=\s*(\d+) old≤250 new_pairs=(\d+) old_roots=(\d+) sign_calls=(\d+) exact_fallback=(\d+) '
    )
    files = ('output-250.txt','rolling-output-250.txt','independent-rolling-replay.txt')
    for name in files:
        log = ROOT/name
        if not log.exists() or 'TOTAL' not in log.read_text():
            continue
        rows = [tuple(map(int,m.groups()))
                for line in log.read_text().splitlines() if (m := line_re.match(line))]
        assert len(rows) == 59
        assert sorted(row[0] for row in rows) == list(range(4,63))
        for k,pairs,roots,_,_ in rows:
            assert pairs == 251-4*k
            assert roots == sum(n-2 for n in range(4*k,251))
        counters[name] = sorted(rows)
        assert tuple(map(sum, zip(*(row[1:] for row in rows)))) == (
            7021,1190089,4603257,3
        )
    assert counters['output-250.txt'] == counters['rolling-output-250.txt']
    if 'independent-rolling-replay.txt' in counters:
        assert counters['independent-rolling-replay.txt'] == counters['output-250.txt']
    return len(counters)


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O.')
    print(f'Coverage verified from {inspect_logs()} full logs, separately at all 59 thresholds.',flush=True)
    print(f'Brute permutation vectors through size eight: {brute_excedances()}.',flush=True)
    print(f'Explicit cycle partition vectors matched from actual certifier: {certify_script_rows()}.',flush=True)
    print(f'Original-variable joint Sturm intervals: {sum(direct_interlacing(n,k) for n,k in LOW_PAIRS)} '
          f'across {len(LOW_PAIRS)} sample consecutive pairs.',flush=True)
