from fractions import Fraction

def add(left, right):
    out = [0] * max(len(left), len(right))
    for poly in (left, right):
        for i, value in enumerate(poly):
            out[i] += value
    while out and not out[-1]:
        out.pop()
    return out

def step(nonrise, rise):
    total = [add(f, r) for f, r in zip(nonrise, rise)]
    drop = [add(f, [0] + r) for f, r in zip(nonrise, rise)]
    suffix = [[] for _ in range(len(total) + 1)]
    for h in reversed(range(len(total))):
        suffix[h] = add(drop[h], suffix[h + 1])
    updated = [add(total[h], suffix[h + 1]) for h in range(len(total))]
    return updated + [[]], [[]] + total, drop, suffix

def sturm(poly):
    p = list(map(Fraction, poly))
    q = [i*p[i] for i in range(1, len(p))]
    sequence = [p, q]
    while len(q) > 1:
        remainder = p.copy()
        while len(remainder) >= len(q):
            scale = remainder[-1] / q[-1]
            shift = len(remainder) - len(q)
            for i, value in enumerate(q):
                remainder[i + shift] -= scale * value
            while remainder and not remainder[-1]:
                remainder.pop()
        assert remainder
        p, q = q, [-value for value in remainder]
        sequence.append(q)
    return tuple(tuple((1 if q[-1] > 0 else -1) * (side ** (len(q)-1))
                       for q in sequence) for side in (-1, 1))

nonrise, rise = [[1]], [[]]
for n in range(1, 16):
    nonrise, rise, drop, suffix = step(nonrise, rise)
    if n == 3:
        assert nonrise[0] == [2, 3]
    if n == 4:
        assert nonrise[0] == [5, 8, 1]
        x = Fraction(-2, 3)
        assert sum(c*x**i for i, c in enumerate(nonrise[0])) == Fraction(1, 9)
        assert drop[1] == [2, 2, 1] and 2**2 - 4*2 == -4
assert suffix[6] == [19791, 75285, 96525, 46635, 6795, 126]
assert sturm(suffix[6]) == ((-1, 1, -1, 1, -1, -1), (1, 1, 1, 1, 1, -1))
assert nonrise[5] == [66255, 207069, 211053, 78755, 8775, 126]
assert sturm(nonrise[5]) == ((-1, 1, -1, 1, -1, 1), (1, 1, 1, 1, 1, 1))
print("Verified: legal drop-only suffix has 3 real roots; full tied transition has 5.")
