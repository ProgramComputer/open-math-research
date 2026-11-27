import argparse, hashlib, json
from math import comb, gcd


def prim(a):
    while a and a[-1] == 0:
        a.pop()
    g = gcd(*a)
    return [x // g for x in a] if g else []


def rem(a, b):
    a = a[:]
    while a and len(a) >= len(b):
        q = a[-1] * (1 if b[-1] > 0 else -1)
        ab = abs(b[-1])
        h = len(a) - len(b)
        a = [x * ab - q * (b[i - h] if i >= h else 0) for i, x in enumerate(a)]
        a = prim(a)
    return a


def index(a, b):
    seq = [a, b]
    while seq[-1]:
        seq.append([-x for x in rem(seq[-2], seq[-1])])
    minus = [p[-1] * (-1) ** (len(p) - 1) for p in seq[:-1]]
    plus = [p[-1] for p in seq[:-1]]
    return sum(a * b < 0 for a, b in zip(minus, minus[1:])) - sum(
        a * b < 0 for a, b in zip(plus, plus[1:])
    )


def run(d, J):
    combinations = [[comb(i, s) for s in range(i + 1)] for i in range((d + 1) * J)]
    counts = [0, 0]
    digest = hashlib.sha256()
    for j in range(2, J):
        # Column recurrence, split by whether the first block is small.
        m = (d + 1) * j
        cols = []
        for k in range(d + 2):
            coeffs = [0] * (m + 1)
            coeffs[0] = int(k == 0)
            for n in range(max(k * j, 1), m + 1):
                row = combinations[n]
                s = sum(
                    row[i] * coeffs[n - i]
                    for i in range(1, min(j, n + 1, n - k * j + 1))
                )
                if k:
                    s += sum(
                        row[i] * cols[k - 1][n - i]
                        for i in range(j, n - (k - 1) * j + 1)
                    )
                coeffs[n] = s
            cols.append(coeffs)
        for n in range(d * j, m):
            a = [cols[k][n] for k in range(d + 1)]
            b = [cols[k][n + 1] for k in range(1 + (n + 1) // j)]
            p, q = prim(a[:]), prim(b[:])
            assert all(x > 0 for x in a + b)
            assert index(p, prim([k * v for k, v in enumerate(p) if k])) == d, (
                j,
                n,
                "Sturm",
            )
            assert index(p, [-x for x in rem(q, p)]) == d, (j, n, "Sturm–Tarski")
            counts[n + 1 == m] += 1
            digest.update(
                (json.dumps([j, n, a, b], separators=(",", ":")) + "\n").encode()
            )
    print(d, J, counts, digest.hexdigest(), flush=True)


if not __debug__:
    raise SystemExit("Run the checker with Python assertions enabled.")

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("d", type=int)
    ap.add_argument("J", type=int)
    a = ap.parse_args()
    run(a.d, a.J)
