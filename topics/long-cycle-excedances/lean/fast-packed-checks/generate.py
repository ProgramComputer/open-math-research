"""Generate authenticated high-size sample endpoints and a row storage comparison."""
import argparse
from hashlib import sha256
import gzip
import json
from math import comb
from pathlib import Path
import re
import runpy

HERE = Path(__file__).resolve().parent
LEDGER = HERE.parents[1] / "intermediate/witness-ledger"
FIRST = runpy.run_path(str(HERE.parent / "packed-shard/generate-packed-shard.py"))
WIDTH = 60
CASES = ((51, 1000, 20), (160, 1000, 2))
ARCHIVE_SHA = "8f8115d4f203840560dd74f7cf12654d0bca00561c8ff473f27ed6af3f20a73e"


def rounded_pair(k, n):
    weights = FIRST["ordinary_eulerian"](k-1)[:WIDTH]
    encode, decode = FIRST["encode"], FIRST["decode"]
    zero = [0] * WIDTH
    rows = [zero] * k + [[encode(v) for v in weights + [0] * (WIDTH-len(weights))]]
    for m in range(k, n+1):
        prior = list(map(decode, rows[m]))
        lag = list(map(decode, rows[m+1-k]))
        scale = comb(m, k-1)
        current = [prior[0]]
        for i in range(1, WIDTH):
            convolution = sum(weights[j]*lag[i-1-j] for j in range(min(i, len(weights))))
            current.append((i+1)*prior[i] + max(m-i, 0)*prior[i-1] + scale*convolution)
        rows.append(list(map(encode, current)))
    return rows[n], rows[n+1]


def selected_archive():
    path = LEDGER / "shards"
    manifest = json.loads((path / "manifest.json").read_text())
    archive = sha256()
    selected = {(k, n): [] for k, n, _ in CASES}
    for item in manifest["shards"]:
        packed = (path / item["file"]).read_bytes()
        if sha256(packed).hexdigest() != item["gzip_sha256"]:
            raise ValueError(f"Unexpected archive shard {item['file']}")
        data = gzip.decompress(packed)
        archive.update(data)
        for line in data.splitlines():
            n, k, rest = line.split(b",", 2)
            key = (int(k), int(n))
            if key in selected:
                selected[key].append(tuple(map(int, rest.split(b","))))
    if archive.hexdigest() != ARCHIVE_SHA:
        raise ValueError("Unexpected witness archive digest")
    return selected


def lean_list(items):
    return "[" + ", ".join(map(str, items)) + "]"


def generate_samples(output):
    selected = selected_archive()
    definitions = ["import HighSizePoint\n\n"
                   "namespace OpenMathResearch.LongCycleExcedances.FastPointSamples\n"]
    for k, n, count in CASES:
        probes = []
        for j, p, pbits, q, qbits in selected[k,n]:
            s = 1 if j % 2 else -1
            for upper, numerator, bits, sign in (
                    (False, p, pbits, s), (False, q, qbits, -s),
                    (True, p, pbits, -s), (True, q, qbits, -s)):
                level = bits - numerator.bit_length()
                probes.append(f"  ⟨{str(upper).lower()}, {numerator}, {bits}, {level}, {sign}⟩")
        if len(probes) != count * 4:
            raise ValueError(f"Unexpected sample count for ({k}, {n})")
        old, next_ = rounded_pair(k, n)
        definitions.append(f"def pair{k} : Pair := ⟨{k}, {n}, {lean_list(old)}, {lean_list(next_)}⟩\n"
                           f"def probes{k} : List Probe := [\n" + ",\n".join(probes) + "]\n")
    definitions.append("end OpenMathResearch.LongCycleExcedances.FastPointSamples\n")
    (output / "HighSizeData.lean").write_text("\n".join(definitions))


def generate_storage(output):
    parts = output / "first"
    FIRST["write"](parts, LEDGER / "shard.csv")
    control = (parts / "PackedRowData.lean").read_text()
    (output / "PackedRowData.lean").write_text(control)
    transformed = control.replace("import PackedRowCore\n",
                                  "import PackedRowCore\nimport RowWordStorage\n")
    namespace = "OpenMathResearch.LongCycleExcedances.PackedShard"
    transformed = transformed.replace(f"namespace {namespace}\n", f"namespace {namespace}.StoredWords\n")
    transformed = transformed.replace(f"end {namespace}\n", f"end {namespace}.StoredWords\n")

    def collapse(match):
        name, raw = match.groups()
        words = list(map(int, raw.split(", ")))
        if len(words) != 50 or any(not 0 <= word < 2**64 for word in words):
            raise ValueError(f"Unexpected storage row {name}")
        packed = sum(word << (64*i) for i, word in enumerate(words))
        recovered = [(packed >> (64*i)) % 2**64 for i in range(len(words))]
        if recovered != words:
            raise ValueError(f"Packing failed to round-trip {name}")
        return f"private def {name} : List ℕ := unpackWordRow 50 {packed}"

    transformed, count = re.subn(r"private def (row\d+) : List ℕ := \[([^\]]+)\]", collapse, transformed)
    if count != 244:
        raise ValueError("Unexpected first-shard row count")
    (output / "PackedWordData.lean").write_text(transformed)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True)
    generate_samples(args.output)
    generate_storage(args.output)
