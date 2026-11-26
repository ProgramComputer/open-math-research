"""Replay the exact pending-state obstructions for the Motzkin transfer."""
from functools import cache
from itertools import zip_longest
from fractions import Fraction

ZERO = (0,)


def add(*polys):
    return tuple(sum(cs) for cs in zip_longest(*polys, fillvalue=0))


def times(q, n):
    return tuple(n*c for c in q)


def at(row, h):
    return row[h] if 0 <= h < len(row) else ZERO


def B(row):
    return [add(at(row, h), at(row, h+1)) for h in range(len(row))]


def pending(f, p):
    return [add(at(f, h), at(f, h-1), (0, *at(p, h)))
            for h in range(len(f)+1)]


@cache
def actual(n):
    if n == 0:
        return [(1,)]
    return B(pending(actual(n-1), actual(n-2) if n > 1 else []))


def trim(p):
    return p[:next((i+1 for i in reversed(range(len(p))) if p[i]), 0)]


def normalized(row):
    return [trim(p) for p in row]


def root_labels(*rows):
    result = []
    for a, row in enumerate(rows):
        for h, p in enumerate(normalized(row)):
            assert p and len(p) <= 2
            if len(p) == 2:
                result.append((Fraction(-p[0], p[1]), (a, h)))
    return [label for _, label in sorted(result)]


def discriminant(p):
    a, b, c = trim(p)
    return b*b-4*a*c


def main():
    p, f = normalized(actual(2)), normalized(actual(3))
    w, z = normalized(pending(p, actual(1))), normalized(pending(actual(1), actual(0)))
    assert f == [(14, 5), (14, 2), (6,), (1,)]
    assert p == [(5, 1), (4,), (1,)]
    assert w == [(5, 3), (9, 2), (5,), (1,)] and z == [(2, 1), (3,), (1,)]
    assert B(w) == f and B(z) == p

    f1 = f.copy()
    p1 = p.copy()
    f1[1] = times(f[1], 50)
    p1[0] = times(p[0], 20)
    out = trim(B(pending(f1, p1))[0])
    assert out == (728, 214, 20)
    assert discriminant(out) == -12444

    w2 = w.copy()
    w2[2] = (100,)
    f2 = B(w2)
    assert f2 == [(14, 5), (109, 2), (101,), (1,)]
    assert root_labels(f2, p, w2, z) == root_labels(f, p, w, z)
    out2 = trim(B(pending(f2, p))[0])
    assert out2 == (137, 21, 1)
    assert discriminant(out2) == -107

    p3 = p.copy()
    p3[2] = (100,)
    w3 = pending(p3, actual(1))
    f3 = B(w3)
    assert root_labels(f3, p3, w3, actual(1)) == root_labels(f, p, w, actual(1))
    out3 = trim(B(pending(f3, p3))[0])
    assert out3 == (141, 21, 1)
    assert discriminant(out3) == -123
    print(out, out2, out3)


if __name__ == "__main__":
    main()
