"""Integer certificates on n = 2j for a common positive weight per block."""
from math import comb, gcd


def by_first_block(j, exponent):
    """Return coefficients after multiplying the row by (2**exponent)**n."""
    rows = [[1]]
    for n in range(1, 2*j + 1):
        row = [0] * (1 + n // j)
        for size in range(1, n + 1):
            offset = int(size >= j)
            scale = comb(n, size) << (exponent * (size - 1))
            for i, coefficient in enumerate(rows[n-size]):
                row[i+offset] += coefficient * scale
        rows.append(row)
    return rows[-1]


def by_surjections(j, exponent):
    """Count all assignments and distinguished large fibers of each onto map."""
    n = 2*j
    onto = [[0] * (n+1) for _ in range(n+1)]
    onto[0][0] = 1
    for a in range(1, n+1):
        for h in range(1, a+1):
            onto[a][h] = h * (onto[a-1][h] + onto[a-1][h-1])
    row = [0, 0, 0]
    for h in range(1, n+1):
        marked = h * sum(comb(n, s) * onto[n-s][h-1] for s in range(j, n+1))
        two = comb(n, j) if h == 2 else 0
        one = marked - 2*two
        none = onto[n][h] - one - two
        for i, count in enumerate((none, one, two)):
            assert count >= 0
            row[i] += count << (exponent*(n-h))
    return row


def sign(a):
    return (a > 0) - (a < 0)


def checked(j, exponent):
    row = by_first_block(j, exponent)
    assert row == by_surjections(j, exponent)
    a, b, c = row
    assert c == comb(2*j, j) << (exponent*(2*j-2))
    return row, sign(b*b - 4*a*c)


if __name__ == '__main__':
    weighted_signs = {}
    for j in range(2, 101):
        row, s = checked(j, j)
        weighted_signs.setdefault(s, []).append(j)
        assert checked(j, 0)[1] == 1
    print('weight 1: positive discriminant for n=2j, j=2..100')
    for s, js in sorted(weighted_signs.items()):
        print(f'weight 2^(-j): discriminant sign {s:+d} at j={js[0]}..{js[-1]} ({len(js)} cases)')
        assert js == list(range(js[0], js[-1]+1))
    first = min(weighted_signs[-1])
    row, _ = checked(first, first)
    common = gcd(*row)
    a, b, c = [x // common for x in row]
    print(f'first negative on the stated diagonal: j={first}, n={2*first}')
    print('primitive coefficients:', a, b, c)
    print('exact discriminant of primitive row:', b*b-4*a*c)
    assert 9**10 > 3*8**10 and 4*(3**10-4)>17**2*201
