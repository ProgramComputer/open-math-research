"""Reproduce all residual row pairs and their exact negative Bezout forms."""

from math import comb, gcd
import argparse, hashlib, json


def negative_bezout_is_pd(old, new):
    d = len(old) - 1
    r = new[:]
    while len(r) >= len(old):
        shift = len(r) - len(old)
        lead = r[-1]
        r = [old[-1] * v for v in r]
        for k, a in enumerate(old):
            r[k + shift] -= lead * a
        r.pop()
    r += [0] * (d + 1 - len(r))
    common = gcd(*r)
    if not common:
        return False
    r = [v // common for v in r]
    mat = [[0] * d for _ in range(d)]
    for a in range(d + 1):
        for b in range(a):
            x = old[b] * r[a] - old[a] * r[b]
            for h in range(a - b):
                mat[a - 1 - h][b + h] += x
    previous = 1
    for i in range(d):
        pivot = mat[i][i]
        if pivot <= 0:
            return False
        for a in range(i + 1, d):
            for b in range(i + 1, d):
                value = pivot * mat[a][b] - mat[a][i] * mat[i][b]
                q, rem = divmod(value, previous)
                assert rem == 0
                mat[a][b] = q
        previous = pivot
    return True


def run(d, J, ledger=None):
    choose = [[comb(n, s) for s in range(n + 1)] for n in range((d + 1) * J)]
    counts = [0, 0]
    digest = hashlib.sha256()
    for j in range(2, J):
        rows = [[1]]
        for n in range(1, (d + 1) * j + 1):
            row = [0] * (n // j + 1)
            for size in range(1, n + 1):
                mul = choose[n][size]
                for k, a in enumerate(rows[n - size]):
                    row[k + (size >= j)] += mul * a
            rows.append(row)
        for n in range(d * j, (d + 1) * j):
            old, new = rows[n], rows[n + 1]
            p = gcd(*old)
            q = gcd(*new)
            assert negative_bezout_is_pd(
                [x // p for x in old], [x // q for x in new]
            ), (j, n)
            counts[n + 1 == (d + 1) * j] += 1
            line = json.dumps([j, n, old, new], separators=(",", ":")) + "\n"
            digest.update(line.encode())
            if ledger:
                ledger.write(line)
    print(
        json.dumps(
            {
                "degree": d,
                "cutoff": J,
                "same_degree": counts[0],
                "carry": counts[1],
                "coefficient_ledger_sha256": digest.hexdigest(),
            }
        )
    )


if not __debug__:
    raise SystemExit("Run the checker with Python assertions enabled.")

if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("degree", type=int)
    ap.add_argument("cutoff", type=int)
    ap.add_argument("--ledger", type=argparse.FileType("w"))
    args = ap.parse_args()
    run(args.degree, args.cutoff, args.ledger)
