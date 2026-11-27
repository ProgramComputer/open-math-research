"""Partition the canonical ledger into deterministic gzip files and record threshold hashes."""
import argparse
import gzip
import hashlib
import json
import sys
from pathlib import Path

CAP = 3_000_000
KMIN = 7
KMAX = 250


def archive(source, dest):
    dest.mkdir()
    thresholds = {
        k: {'gaps': 0, 'bytes': 0, 'digest': hashlib.sha256()} for k in range(KMIN, KMAX+1)
    }
    files = []
    whole = hashlib.sha256()
    out = handle = None
    try:
        for line in source:
            k = int(line.split(b',', 2)[1])
            if out is None or item['bytes'] + len(line) > CAP:
                if out is not None:
                    out.close()
                    handle.close()
                name = f'part-{len(files)+1:02d}.csv.gz'
                handle = (dest/name).open('wb')
                out = gzip.GzipFile(filename='', mode='wb', fileobj=handle, mtime=0)
                item = {'file': name, 'bytes': 0, 'gaps': 0}
                files.append(item)
            out.write(line)
            item['bytes'] += len(line)
            item['gaps'] += 1
            thresholds[k]['gaps'] += 1
            thresholds[k]['bytes'] += len(line)
            thresholds[k]['digest'].update(line)
            whole.update(line)
    finally:
        if out is not None:
            out.close()
            handle.close()
    for item in files:
        data = (dest/item['file']).read_bytes()
        item['gzip_bytes'] = len(data)
        item['gzip_sha256'] = hashlib.sha256(data).hexdigest()
    receipt = {
        'stream_sha256': whole.hexdigest(),
        'shards': files,
        'thresholds': [
            dict(k=k, gaps=t['gaps'], bytes=t['bytes'], sha256=t['digest'].hexdigest())
            for k,t in thresholds.items()
        ],
    }
    (dest/'manifest.json').write_text(json.dumps(receipt, indent=2)+'\n')


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('destination',type=Path)
    archive(sys.stdin.buffer,parser.parse_args().destination)
