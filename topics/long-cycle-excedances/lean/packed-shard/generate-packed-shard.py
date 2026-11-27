"""Emit independent short kernel checks for the cutoff-13 packed-row shard."""

import argparse
import csv
import hashlib
from math import comb
from pathlib import Path

CUTOFF = 13
BITS = 48
WIDTH = 50
LAST = 256
BLOCK = 12
SHARD_SHA = "e6b756647fcde23d8047abf9968340c6787f22a62cba54d59b3a917e43c628d0"
NS = "OpenMathResearch.LongCycleExcedances.PackedShard"


def ordinary_eulerian(m):
    row = [1]
    for n in range(1, m + 1):
        current = [0] * n
        for j, count in enumerate(row):
            current[j] += (j + 1) * count
            if j + 1 < n:
                current[j + 1] += (n - 1 - j) * count
        row = current
    return row


def encode(value):
    shift = max(0, value.bit_length() - BITS)
    assert shift < 2**16
    return (shift << BITS) + (value >> shift)


def decode(word):
    return (word % 2**BITS) << (word >> BITS)


def packed_rows():
    weights = ordinary_eulerian(CUTOFF - 1)
    assert len(weights) == CUTOFF - 1
    zero = [0] * WIDTH
    rows = [zero] * CUTOFF
    rows.append([encode(a) for a in weights + [0] * (WIDTH - len(weights))])
    for n in range(CUTOFF, LAST):
        prior = [decode(word) for word in rows[n]]
        lag = [decode(word) for word in rows[n + 1 - CUTOFF]]
        choose = comb(n, CUTOFF - 1)
        new = [prior[0]]
        for i in range(1, WIDTH):
            convolution = sum(weights[j] * lag[i - 1 - j] for j in range(min(i, len(weights))))
            new.append((i + 1) * prior[i] + max(n - i, 0) * prior[i - 1] + choose * convolution)
        rows.append([encode(a) for a in new])
    return rows


def signed_test(row, n, p, bits, direction):
    denominator = 1 << bits
    rounded = upper = 0
    for word in reversed(row):
        value = decode(word)
        rounded = value - p * rounded // denominator
        upper = value - (-(p * upper) // denominator)
    margin = direction * rounded - 2 + (-upper // (2**36))
    u, v = (WIDTH + 1)**n, (WIDTH + 2)**n
    z = denominator * u - p * v
    return (
        0 < p and 2 * p <= denominator and z > 0
        and denominator * u**2 * p**WIDTH < margin * denominator**WIDTH * z
    )


def verify_shard(path, rows):
    assert hashlib.sha256(path.read_bytes()).hexdigest() == SHARD_SHA
    with path.open(newline="") as archive:
        records = [tuple(map(int, rec)) for rec in csv.reader(archive)]
    assert len(records) == 131
    counts = {n: 0 for n in range(251, 256)}
    for n, k, j, a, ab, b, bb in records:
        assert k == CUTOFF and n in counts
        counts[n] += 1
        s = (-1)**(j - 1)
        assert signed_test(rows[n], n, a, ab, s)
        assert signed_test(rows[n], n, b, bb, -s)
        assert signed_test(rows[n + 1], n + 1, a, ab, -s)
        assert signed_test(rows[n + 1], n + 1, b, bb, -s)
    assert list(counts.values()) == [26, 26, 26, 26, 27], counts
    print(f"Independently checked all {sum(counts.values()) * 4} packed Boolean tests in Python.")


def write(output, archive):
    output.mkdir(parents=True)
    rows = packed_rows()
    verify_shard(archive, rows)
    manifest = []

    def module(name, source):
        filename = name + ".lean"
        raw = source.encode("utf-8")
        (output / filename).write_bytes(raw)
        manifest.append(f"{hashlib.sha256(raw).hexdigest()}  {filename}\n")

    definitions = "\n".join(
        f"private def row{n} : List ℕ := [{', '.join(map(str, rows[n]))}]"
        for n in range(CUTOFF, LAST + 1)
    )

    def lookup(lo, hi, depth=2):
        if hi - lo == 1:
            return f"row{lo}"
        mid = (lo + hi) // 2
        pad = " " * depth
        return (f"if n < {mid} then\n{pad}  {lookup(lo, mid, depth+2)}"
                f"\n{pad}else\n{pad}  {lookup(mid, hi, depth+2)}")

    module("PackedRowData", f"""import PackedRowCore

namespace {NS}

{definitions}

def packedRow (n : ℕ) : List ℕ :=
  if n < 13 ∨ 256 < n then [] else
    {lookup(CUTOFF, LAST+1, 4)}

theorem packedRow_short (n : ℕ) (h : n < 13) : packedRow n = [] := if_pos (Or.inl h)

def packedStepOK (n : ℕ) : Bool :=
  rowMatches (fastValue n (packedRow n) (packedRow (n+1-13))) (packedRow (n+1))

set_option maxRecDepth 10000 in
theorem packedRow_seed : rowMatches weight (packedRow 13) = true := by decide

#print axioms packedRow_seed
end {NS}
""")

    row_blocks = []
    for start in range(CUTOFF, LAST, BLOCK):
        stop = min(start + BLOCK, LAST)
        name = f"PackedSteps{start:03d}"
        theorem = f"packedSteps{start}"
        row_blocks.append((name, theorem, stop))
        module(name, f"""import PackedRowData

namespace {NS}

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 4096 in
set_option maxHeartbeats 0 in
private theorem checks : ((List.range {stop-start}).map
    (fun i => {start}+i)).all packedStepOK = true := by decide

theorem {theorem} (n : ℕ) (lo : {start} ≤ n) (hi : n < {stop}) :
    packedStepOK n = true := by
  have hmem : n ∈ (List.range {stop-start}).map (fun i => {start}+i) :=
    List.mem_map.mpr ⟨n-{start}, List.mem_range.mpr (by omega), by omega⟩
  exact List.all_eq_true.mp checks n hmem

#print axioms {theorem}
end {NS}
""")

    imports = "".join(f"import {name}\n" for name, _, _ in row_blocks)
    proof = "".join(f"  by_cases h{stop} : n < {stop}\n"
                    f"  · exact {theorem} n (by omega) h{stop}\n"
                    for _, theorem, stop in row_blocks[:-1])
    proof += f"  exact {row_blocks[-1][1]} n (by omega) hi"
    module("PackedRowSteps", f"""{imports}
namespace {NS}

theorem packedSteps (n : ℕ) (lo : 13 ≤ n) (hi : n < 256) :
    packedStepOK n = true := by
{proof}

#print axioms packedSteps
end {NS}
""")
    for n in range(251, 256):
        module(f"PackedEndpoints{n}", f"""import PackedShardTest

namespace {NS}

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 4096 in
set_option maxHeartbeats 0 in
theorem checks{n} : (shardSlice {n}).all gapOK = true := by decide

#print axioms checks{n}
end {NS}
""")

    (output / "SHA256SUMS").write_text("".join(manifest), encoding="ascii")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="new directory for generated Lean sources")
    parser.add_argument("shard", type=Path, help="checked archive shard CSV")
    args = parser.parse_args()
    write(args.output, args.shard)
