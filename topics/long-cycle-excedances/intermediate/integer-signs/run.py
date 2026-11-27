"""Replay and authenticate the complete canonical witness archive."""

import argparse
import gzip
import subprocess
from hashlib import sha256
from pathlib import Path
from time import monotonic

STREAM_BYTES = 63_014_205
STREAM_SHA256 = "8f8115d4f203840560dd74f7cf12654d0bca00561c8ff473f27ed6af3f20a73e"


def run(shards, checker):
    started = monotonic()
    digest = sha256()
    size = 0
    with subprocess.Popen([checker.resolve()], stdin=subprocess.PIPE) as check:
        for part in sorted(shards.glob("part-*.csv.gz")):
            with gzip.open(part, "rb") as stream:
                while chunk := stream.read(256 * 1024):
                    digest.update(chunk)
                    size += len(chunk)
                    check.stdin.write(chunk)
            print(part.name, round(monotonic() - started, 2), flush=True)
        check.stdin.close()
        if check.wait() != 0:
            raise SystemExit("Sign verification failed.")
    if size != STREAM_BYTES or digest.hexdigest() != STREAM_SHA256:
        raise SystemExit("The supplied records differ from the complete reviewed ledger.")
    print(size, digest.hexdigest(), "seconds", round(monotonic() - started, 2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("shards", type=Path)
    parser.add_argument("checker", type=Path)
    args = parser.parse_args()
    run(args.shards, args.checker)
