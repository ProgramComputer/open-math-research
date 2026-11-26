"""Direct enumeration of short and long tile histories, including open tiles."""
from collections import Counter
from fractions import Fraction

STOP = 3

# (duration, change of height of first half, change of height of second half, mark)
TILES = tuple((1, first, second, 0) for first in (0, 1) for second in (0, -1))
TILES += tuple((2, 0, second, 1) for second in (0, -1))


def enumerate_histories():
    finished, pending = Counter(), Counter()

    def visit(time, height, marks):
        finished[time, height, marks] += 1
        # Count open tiles once, before making either possible closing choice.
        pending[time, height, marks] += 1
        pending[time, height+1, marks] += 1
        if time+1 <= STOP:
            pending[time+1, height, marks+1] += 1
        for duration, first, second, mark in TILES:
            final_height = height+first+second
            if time+duration <= STOP and final_height >= 0:
                visit(time+duration, final_height, marks+mark)

    visit(0, 0, 0)
    return finished, pending


def layer(table, time):
    output = []
    for h in range(1+max(h for t, h, k in table if t == time)):
        degree = max(k for t, height, k in table if (t, height) == (time, h))
        output.append(tuple(table[time, h, k] for k in range(degree+1)))
    return output


def main():
    complete, open_tiles = enumerate_histories()
    assert layer(complete, 1) == [(2,), (1,)]
    assert layer(complete, 2) == [(5, 1), (4,), (1,)]
    assert layer(complete, 3) == [(14, 5), (14, 2), (6,), (1,)]
    assert layer(open_tiles, 1) == [(2, 1), (3,), (1,)]
    assert layer(open_tiles, 2) == [(5, 3), (9, 2), (5,), (1,)]

    genuine_nonzero_roots = [Fraction(-14, 2), Fraction(-5), Fraction(-9, 2),
                             Fraction(-14, 5), Fraction(-2), Fraction(-5, 3)]
    assert sorted(set(genuine_nonzero_roots)) == genuine_nonzero_roots
    assert Fraction(-109, 2) < genuine_nonzero_roots[1]
    assert Fraction(-113, 2) < genuine_nonzero_roots[1]

    # Evaluate the next height-zero coefficients by closing tiles directly.
    # For a short tile, height 0 offers two legal closures to 0 and height 1 one.
    # For a long tile, heights 0 and 1 each offer one legal closure to 0.
    for f0, f1, p0, p1, expected in (
        ((14, 5), (700, 100), (100, 20), 4, -12444),
        ((14, 5), (109, 2), (5, 1), 4, -107),
        ((14, 5), (113, 2), (5, 1), 4, -123),
    ):
        c0 = 2*f0[0]+f1[0]
        c1 = 2*f0[1]+f1[1]+p0[0]+p1
        c2 = p0[1]
        assert c1*c1-4*c0*c2 == expected
    print("direct tile enumeration and three discriminants agree")


if __name__ == "__main__":
    main()
