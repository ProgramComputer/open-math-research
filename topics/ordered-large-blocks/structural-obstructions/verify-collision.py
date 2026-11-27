"""Check the supplementary-box obstruction using two independent labeled counters."""
import gzip
import json
from math import comb, gcd
from pathlib import Path


def short_tail(j):
    n = 2 * j
    center = comb(n, j)
    tail = sum(comb(n, s) * 2 ** (n - s) for s in range(j, n + 1))
    two = [0, 4 ** j - center, center]
    three = [9 ** j - 3 * tail + 3 * center, 3 * tail - 6 * center, 3 * center]
    return two, three


def allocate(j, boxes):
    n = 2 * j
    counts = [0, 0, 0]
    if boxes == 2:
        for a in range(n + 1):
            counts[int(a >= j) + int(n - a >= j)] += comb(n, a)
    elif boxes == 3:
        for a in range(n + 1):
            for b in range(n - a + 1):
                c = n - a - b
                counts[int(a >= j) + int(b >= j) + int(c >= j)] += comb(n, a) * comb(n - a, b)
    else:
        raise ValueError(boxes)
    return counts


def discriminant(f):
    a, b, c = f
    return b * b - 4 * a * c


def verify(file=None):
    rows = []
    for j in range(2, 129):
        two, three = short_tail(j)
        assert two == allocate(j, 2) and three == allocate(j, 3)
        prefix = [0, 4 + 2 * two[1], 2 * two[2]]
        complete = [p + q for p, q in zip(prefix, three)]
        intermediate = [(1 << j) * p + q for p, q in zip(prefix, three)]
        assert discriminant(prefix) > 0 and discriminant(complete) > 0
        assert (discriminant(intermediate) < 0) == (j >= 16)
        assert discriminant(intermediate) != 0
        rows.append([j, two, three, prefix, intermediate, complete, discriminant(intermediate)])
    smallest = rows[16 - 2][4]
    primitive = [c // gcd(*smallest) for c in smallest]
    assert primitive == [547901605735920, 231159571069429, 26262204039750]
    assert discriminant(primitive) == -4121667757171163267992893959
    j = 128
    assert 12 * 8 ** j <= 9 ** j
    assert 4 * 9 ** j > 81 * (2 * j + 1) * 8 ** j
    assert 9 * 16 ** j > 80 * (2 * j + 1) * 9 ** j
    assert 9 * (2 * j + 1) > 8 * (2 * j + 3)
    if file is not None:
        with file.open('wb') as out, gzip.GzipFile(filename='', fileobj=out, mode='wb', mtime=0) as stream:
            for row in rows:
                stream.write((json.dumps(row, separators=(',', ':')) + '\n').encode('ascii'))
    print('Two counters agree at every threshold 2 through 128.')
    print('Both end discriminants are strictly positive on that range.')
    print('First negative intermediate discriminant at j = 16.')
    print(f'Primitive polynomial at j = 16: {primitive}; discriminant {discriminant(primitive)}.')
    print('All four exact initial bounds used for the infinite tail passed.')


if __name__ == '__main__':
    import argparse
    if not __debug__:
        raise SystemExit('The verifier requires enabled assertions.')
    arg = argparse.ArgumentParser()
    arg.add_argument('--ledger', type=Path)
    verify(arg.parse_args().ledger)
