"""Exact whole-row root brackets for the three-cycle band through old size 191."""
from argparse import ArgumentParser
from gzip import GzipFile
from hashlib import sha256
from json import loads
from math import comb
from multiprocessing import Pool
from pathlib import Path
from runpy import run_path
from tempfile import TemporaryDirectory


def setup(topic):
    global helper, eulerian, base
    helper = run_path(str(topic / 'verify_two_cycle_band.py'))
    eulerian = helper['eulerian_rows'](191)
    base = helper['independent_eulerian_brackets'](eulerian, 126)


def verify_threshold(task):
    k, folder, full = task
    t = helper['T']
    signs = helper['Signs']
    check = helper['check']
    transfer = helper['refine_and_transfer']
    old_size_limit = min(4*k - 1, 191)
    # Distinguish the cycle of label 1. A residual cycle system contributes t*Q.
    rows = {}
    pairs = roots = 0
    path = folder / f"k{k:02d}.jsonl.gz"
    digest = sha256()
    with path.open('xb') as raw, GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as ledger:
        for n in range(k, old_size_limit + 2):
            new = eulerian[n - 1]
            for length in range(k, n - k + 1):
                new += comb(n - 1, length - 1) * t * eulerian[length - 1] * rows[n - length]
            rows[n] = new
            if n == 2*k - 1:
                brackets = base[n - 1]
            if n < 2*k:
                continue
            size = n - 1
            old = rows[size]
            lag = comb(size, k - 1) * t * eulerian[k - 1] * rows[n - k]
            check(new == t*(1-t)*old.derivative() + (1+(size-1)*t)*old + lag,
                  (size, k, "insertion recurrence"))
            old_sign, plus = signs(old, size - 2), signs(new, size - 1)
            if size < 3*k - 1:
                _, brackets = transfer(old_sign, (plus,), brackets, (size,k))
                continue
            minus = signs(new - 2*lag, size - 1)
            refined, brackets = transfer(old_sign, (plus,minus), brackets, (size,k))
            helper['write_record'](ledger, full, size, k, old_sign, plus, minus, refined, brackets)
            digest.update(helper['json_bytes']([size,k,refined,brackets]))
            pairs += 1
            roots += size - 2
    return k,pairs,roots,digest.hexdigest()


if __name__ == '__main__':
    ap = ArgumentParser(description=__doc__)
    ap.add_argument('--topic', type=Path, default=Path(__file__).resolve().parent)
    ap.add_argument('--ledger', type=Path, help='retain generated per-threshold JSONL files')
    ap.add_argument('--workers', type=int, default=1)
    ap.add_argument('--full', action='store_true', help='include all coefficients and endpoints')
    args = ap.parse_args()
    if args.workers < 1: ap.error('workers must be positive')
    temporary = TemporaryDirectory() if args.ledger is None else None
    if temporary is not None:
        args.ledger = Path(temporary.name)
    args.ledger.mkdir(exist_ok=True, parents=True)
    tasks = [(k,args.ledger,args.full) for k in range(3,65)]
    expected = [(n,k) for k,_,_ in tasks for n in range(3*k-1,min(4*k-1,191)+1)]
    counts = []
    with Pool(args.workers, initializer=setup, initargs=(args.topic,)) as pool:
        for row in pool.imap(verify_threshold,tasks):
            counts.append(row)
            print(*row,flush=True)
    actual = sum(r[1] for r in counts), sum(r[2] for r in counts)
    if actual != (len(expected),sum(n-2 for n,k in expected)):
        raise ArithmeticError(('coverage',actual))
    from gzip import open as open_gzip
    with open_gzip(args.topic / 'three-cycle-small-pairs.jsonl.gz', 'rt') as archive:
        for k, _, _ in tasks:
            with open_gzip(args.ledger / f'k{k:02d}.jsonl.gz', 'rt') as shard:
                for line in shard:
                    witness = loads(next(archive))
                    record = loads(line)
                    if any(record.get(key) != val for key, val in witness.items()):
                        raise ArithmeticError(('certificate replay', k, record['n']))
        if next(archive, None) is not None:
            raise ArithmeticError('unused ledger rows')
    if temporary is not None:
        temporary.cleanup()
    print('Certified',actual[0],'pairs and both lag signs at',actual[1],'old roots.')
