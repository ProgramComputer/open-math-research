"""Check residual selection, low quotas and Bezoutians by independent methods."""
import argparse
import json
from math import comb
from pathlib import Path

from flint import fmpz_mat
from verify import load_exact_vectors


def residual_keys():
    keys = set()
    for d in range(2,36):
        for r in range(2,d-1):
            degree = 36*r//d
            if degree <= 14 or (r,d) == (2,4):
                continue
            k = min(18,degree-1)
            if ((k+1)*(37-k))**d <= 4*(k*(36-k))**d:
                keys.add((r,d))
    return keys


def assignments(n,r,u,v):
    """Assign u labeled singleton groups and v labeled pair groups to capped rows."""
    ways = {(0,0):1}
    for _ in range(n):
        following = {}
        for (i,j), weight in ways.items():
            for b in range(min(r//2,v-j)+1):
                for a in range(min(r-2*b,u-i)+1):
                    key = i+a,j+b
                    following[key] = following.get(key,0)+weight*comb(i+a,a)*comb(j+b,b)
        ways = following
    return ways.get((u,v),0)


def bezout_positive(v):
    m = len(v)-1
    derivative = [(i+1)*v[i+1] for i in range(m)]+[0]
    bezout = [[0]*m for _ in range(m)]
    for i in range(1,m+1):
        for j in range(i):
            w = v[i]*derivative[j]-derivative[i]*v[j]
            for t in range(i-j):
                bezout[i-1-t][j+t] += w
    for h in range(1,m+1):
        assert fmpz_mat([row[:h] for row in bezout[:h]]).det() > 0
    return m


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--original-partial", type=Path, help="optional working checkpoint")
    args = parser.parse_args()
    loaded = load_exact_vectors()
    if args.original_partial:
        original = {}
        for line in args.original_partial.read_text().splitlines():
            row = json.loads(line)
            if "coefficients" in row:
                original[row["r"],row["d"]] = row["coefficients"]
        reviewed = [(key, coeff) for key,(coeff, source) in loaded.items()
                    if source == "earlier partial replay"]
        assert len(reviewed) == 15
        assert all(original[key] == coeff for key, coeff in reviewed)
    assert set(loaded) == residual_keys() and len(loaded) == 28
    roots = 0
    for (r,d), (v, _) in sorted(loaded.items()):
        assert v[1] == assignments(36,r,d,0)
        assert v[2]*2**d == sum((-1)**b*comb(d,b)*assignments(36,r,2*(d-b),b)
                                for b in range(d+1))
        roots += bezout_positive(v)
    assert roots == 617
    print("28 residual triples, 56 independent endpoint-group counts,",
          roots, "strictly positive leading Bezoutian minors")


if __name__ == "__main__":
    main()
