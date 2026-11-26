"""Reconstruct all three whole-polynomial coefficient vectors in each small certificate."""
import gzip
from hashlib import sha256
import json
from pathlib import Path
from runpy import run_path

from flint import fmpz_poly


def digest(poly):
    data = json.dumps(list(map(int, poly.coeffs())), separators=(',', ':')).encode('ascii')
    return sha256(data).hexdigest()


def main():
    topic = Path(__file__).resolve().parent
    cycle_counts = run_path(str(topic / 'three_cycle_prefix.py'))['band_prefixes']
    rows_by_k = dict(cycle_counts(192, 192, first_n=8))
    t = fmpz_poly([0, 1])
    pairs = roots = 0
    keys = ('old_coefficients', 'positive_pencil_coefficients', 'negative_pencil_coefficients')
    with gzip.open(topic / 'three-cycle-small-pairs.jsonl.gz', 'rt') as archive:
        for k in range(3, 65):
            rows = rows_by_k[k]
            for n in range(3*k - 1, min(4*k - 1, 191) + 1):
                record = json.loads(next(archive))
                if (record['n'], record['k']) != (n, k):
                    raise ArithmeticError(('ledger coverage', n, k))
                p, q = rows[n], rows[n + 1]
                unmarked = t * (1 - t) * p.derivative() + (1 + (n - 1)*t) * p
                for key, poly in zip(keys, (p, q, 2*unmarked - q)):
                    if digest(poly) != record[key + '_sha256']:
                        raise ArithmeticError((n, k, key))
                pairs += 1
                roots += n - 2
        if next(archive, None) is not None or (pairs, roots) != (1595, 198819):
            raise ArithmeticError(('unexpected total', pairs, roots))
    print(f'Independent cycle counts matched all {3*pairs} whole vectors for {pairs} pairs.')


if __name__ == '__main__':
    main()
