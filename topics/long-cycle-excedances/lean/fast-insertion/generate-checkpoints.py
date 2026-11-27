"""Generate sequential, strictly checkable Lean checkpoint modules."""
import argparse
import hashlib
from math import comb
from pathlib import Path

CUTOFF = 13
WIDTH = 61
FINAL_SIZE = 252
NAMESPACE = "OpenMathResearch.LongCycleExcedances.InsertionTable"
HEADER = f"""namespace {NAMESPACE}
set_option maxHeartbeats 0
set_option maxRecDepth 10000

"""
MODEL = """
open Polynomial

/-- Polynomial facts supplied by the literal permutation recurrence. -/
structure CheckpointModel where
  A : ℝ[X]
  E : ℕ → ℝ[X]
  a_agrees : agrees 61 checkpointEulerian A
  zero_row : E 0 = 1
  successor : ∀ n, E (n+1) =
    C (n : ℝ)*X*E n + X*(1-X)*derivative (E n) +
      C (n.choose 12 : ℝ)*(X*A)*E (n+1-13)

theorem agrees_checkpoint0 (model : CheckpointModel) : agrees 61 checkpoint0 (model.E 0) := by
  have hstart : start 61 = checkpoint0 := by decide
  intro i hi
  rw [← hstart, start, entry_rowOf _ _ _ hi, model.zero_row, coeff_one]
  split <;> norm_num

"""
FINAL = """
theorem checkpoint_first_pair (model : CheckpointModel) :
    agrees 61 checkpoint251 (model.E 251) ∧ agrees 61 checkpoint252 (model.E 252) :=
  ⟨agrees_checkpoint251 model, agrees_checkpoint252 model⟩

#print axioms checkpoint_step0
#print axioms checkpoint_step251
#print axioms checkpoint_first_pair
"""


def lag(n):
    return max(0, n + 1 - CUTOFF)


def witness_rows():
    m = CUTOFF - 1
    a = [
        sum((-1) ** v * comb(m + 1, v) * (i + 1 - v) ** m for v in range(i + 1))
        if i < m else 0
        for i in range(WIDTH)
    ]
    rows = [[1] + [0] * (WIDTH - 1)]
    for n in range(FINAL_SIZE):
        p, r = rows[n], rows[lag(n)]
        factor = comb(n, CUTOFF - 1)
        rows.append([0] + [
            (i + 1) * p[i + 1] + (n - i) * p[i]
            + factor * sum(a[j] * r[i - j] for j in range(min(m, i + 1)))
            for i in range(WIDTH - 1)
        ])
    return a, rows


def literal(values):
    return "[" + ", ".join(map(str, values)) + "]"


def model_step(n):
    return f"""theorem agrees_checkpoint{n+1} (model : CheckpointModel) :
    agrees 61 checkpoint{n+1} (model.E {n+1}) := by
  rw [← checkpoint_step{n}]
  exact next_agrees 61 13 {n} _ _ _ model.A _ _ _ model.a_agrees
    (agrees_checkpoint{n} model) (agrees_checkpoint{lag(n)} model) (model.successor {n})

"""


def generate(output, chunk_size):
    output.mkdir(parents=True)
    a, rows = witness_rows()
    manifest = []
    def write(module, source):
        path = output / (module + ".lean")
        raw = source.encode("utf-8")
        path.write_bytes(raw)
        manifest.append(f"{hashlib.sha256(raw).hexdigest()}  {path.name}\n")

    data_span = 12

    def data_module(n):
        return f"CheckpointData{n // data_span:03d}"

    for first in range(0, FINAL_SIZE + 1, data_span):
        data = ["import InsertionTable\n\n", HEADER]
        if first == 0:
            # Out-of-range entries are zero. This Eulerian polynomial has degree eleven.
            data.append(f"def checkpointEulerian : List ℤ := {literal(a[:CUTOFF-1])}\n")
        for n in range(first, min(first + data_span, FINAL_SIZE + 1)):
            data.append(f"def checkpoint{n} : List ℤ := {literal(rows[n])}\n")
        write(data_module(first), "".join(data) + f"end {NAMESPACE}\n")

    modules = []
    for first in range(0, FINAL_SIZE, chunk_size):
        name = f"CheckpointChunk{len(modules):03d}"
        modules.append(name)
        indices = range(first, min(first + chunk_size, FINAL_SIZE))
        dependencies = {data_module(0)}
        for n in indices:
            dependencies.update((data_module(n), data_module(n+1), data_module(lag(n))))
        lines = ["".join(f"import {m}\n" for m in sorted(dependencies)), HEADER]
        for n in range(first, min(first + chunk_size, FINAL_SIZE)):
            lines.append(
                f"theorem checkpoint_step{n} : next 61 13 checkpointEulerian {n} checkpoint{n} "
                f"checkpoint{lag(n)} = checkpoint{n+1} := by decide\n"
            )
        lines.append(f"end {NAMESPACE}\n")
        write(name, "".join(lines))

    imports = "".join(f"import {module}\n" for module in modules)
    proof = [imports, HEADER, MODEL]
    proof.extend(model_step(n) for n in range(FINAL_SIZE))
    proof.append(f"{FINAL}end {NAMESPACE}\n")
    write("CheckpointReplay", "".join(proof))
    (output / "SHA256SUMS").write_bytes("".join(manifest).encode("ascii"))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="new output directory")
    parser.add_argument("--chunk-size", type=int, choices=range(1, 13), default=6)
    args = parser.parse_args()
    generate(args.output, args.chunk_size)
