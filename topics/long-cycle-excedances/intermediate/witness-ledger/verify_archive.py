"""Check a gzip archive against its ordered shard and threshold receipts."""
import argparse
import gzip
import hashlib
import json
import sys
from pathlib import Path

from archive import CAP, KMIN, KMAX


def verify_archive(directory, destination):
    receipt = json.loads((directory/'manifest.json').read_text())
    files = [f'part-{i:02d}.csv.gz' for i in range(1,len(receipt['shards'])+1)]
    if files != sorted(path.name for path in directory.glob('*.csv.gz')):
        raise ValueError('The directory has missing or unlisted shards.')
    hashes = {k: hashlib.sha256() for k in range(KMIN,KMAX+1)}
    count = dict.fromkeys(hashes,0)
    size = dict.fromkeys(hashes,0)
    whole = hashlib.sha256()
    for expected, name in zip(receipt['shards'],files,strict=True):
        path = directory/name
        packed = path.read_bytes()
        if name != expected['file'] or len(packed) != expected['gzip_bytes'] or \
                hashlib.sha256(packed).hexdigest() != expected['gzip_sha256']:
            raise ValueError(f'Packed file mismatch in {name}')
        total = gaps = 0
        with gzip.open(path,'rb') as source:
            for line in source:
                k = int(line.split(b',',2)[1])
                hashes[k].update(line)
                whole.update(line)
                size[k] += len(line)
                count[k] += 1
                total += len(line)
                gaps += 1
                if destination is not None:
                    destination.write(line)
        if not 0 < total <= CAP or total != expected['bytes'] or gaps != expected['gaps']:
            raise ValueError(f'Unpacked shard mismatch in {name}')
    thresholds = [
        dict(k=k, gaps=count[k], bytes=size[k], sha256=hashes[k].hexdigest())
        for k in hashes
    ]
    if thresholds != receipt['thresholds'] or whole.hexdigest() != receipt['stream_sha256']:
        raise ValueError('Threshold or whole-stream mismatch')
    print(f"{len(files)} shards, {sum(count.values())} gaps, {sum(size.values())} CSV bytes, "
          f"{whole.hexdigest()}",file=sys.stderr)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory',type=Path)
    parser.add_argument('--emit',action='store_true')
    args = parser.parse_args()
    verify_archive(args.directory,sys.stdout.buffer if args.emit else None)
