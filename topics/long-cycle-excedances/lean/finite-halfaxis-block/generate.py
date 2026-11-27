"""Generate the shared coefficient/witness data and bounded Lean arithmetic leaves."""
from __future__ import annotations

import argparse
import gzip
from hashlib import sha256
import json
from math import comb
from pathlib import Path

ARCHIVE_SHA = "95f445fa4e7864984c33ca44eb2f83a8295a628721e0b65bf523fb55265490e8"
SEED = [1, 120, 1191, 2416, 1191, 120, 1]
BEGIN = 32
ARCHIVE_END = 251
END = ARCHIVE_END
WIDTH = END - 1
HORNERS_PER_LEAF = 16
CELLS_PER_LEAF = 25
ROWS_PER_FILE = 8


def archive_windows(path):
    raw = gzip.decompress(path.read_bytes())
    if sha256(raw).hexdigest() != ARCHIVE_SHA:
        raise ValueError("Uncompressed compact archive does not match #331")
    iterator = iter(raw.splitlines())
    table = {}
    for n in range(BEGIN, ARCHIVE_END):
        table[n] = []
        for i in range((n - 2) // 2):
            old, rank, a, e, b, f = json.loads(next(iterator))
            if (old, rank) != (n, i) or min(a, e, b, f) < 0:
                raise ValueError((n, i))
            table[n].append((a, e, b, f))
    if next(iterator, None) is not None:
        raise ValueError("Trailing witness lines")
    return table


def coefficient_rows():
    rows = {n: [] for n in range(8)}
    rows[8] = SEED
    for n in range(8, END):
        old = rows[n] + [0]
        lag = rows[n - 7]
        factor = comb(n, 7)
        next_row = [1]
        for i in range(1, n):
            correction = sum(
                SEED[j] * lag[i - 1 - j]
                for j in range(min(i, len(SEED))) if i - 1 - j < len(lag)
            )
            next_row.append((i + 1) * old[i] + (n - i) * old[i - 1] + factor * correction)
        rows[n + 1] = next_row
    return rows


def literal(seq):
    return "[" + ", ".join(map(str, seq)) + "]"


def output(path, imports, lines):
    header = [f"import {name}" for name in imports]
    start = ["", "set_option maxRecDepth 20000", "", "namespace RepositoryQuotientAudit.CutoffEightBlock",
             "open LongCycleFinite", ""]
    end = ["", "end RepositoryQuotientAudit.CutoffEightBlock", ""]
    path.write_text("\n".join(header + start + lines + end))


def chunks(start, stop, width):
    for a in range(start, stop, width):
        yield a, min(a + width, stop)


def write_data(directory, rows, windows, selected):
    modules = []
    for start, end in chunks(8, END + 1, ROWS_PER_FILE):
        wanted = [n for n in range(start, end) if n in selected]
        if not wanted:
            continue
        module = f"FiniteRowData{start:03d}"
        lines = [f"def r{n} : List ℕ := {literal(rows[n])}" for n in wanted]
        for n in wanted:
            if n in windows:
                values = [f"⟨⟨{a}, {e}⟩, ⟨{b}, {f}⟩⟩" for a, e, b, f in windows[n]]
                lines.append(f"def w{n} : List HalfAxisDyadicWindow := {literal(values)}")
        output(directory / (module + ".lean"), ["ArithmeticBlocks"], lines)
        modules.append(module)
    names = [f"r{n}" if n in selected else "[]" for n in range(8, END + 1)]
    ends = [f"w{n}" if n in selected else "[]" for n in range(BEGIN, END)]
    seed_literal = literal(SEED)
    lines = [
        f"def rowTable : List (List ℕ) := {literal(names)}",
        "def row (n : ℕ) : List ℕ := if n < 8 then [] else rowTable[n-8]?.getD []",
        f"def windowTable : List (List HalfAxisDyadicWindow) := {literal(ends)}",
        "def bracket (n i : ℕ) : HalfAxisDyadicWindow :=",
        "  ((windowTable[n-32]?.getD [])[i]?).getD ⟨⟨0, 0⟩, ⟨0, 0⟩⟩",
        f"def weight : ℕ → ℕ := exactListRead {seed_literal}",
        f"private theorem descent_snapshot : descentCoeffs 7 = {seed_literal} := by decide",
        "theorem weight_eq : weight = compactCycleWeight 8 := by",
        "  funext j",
        "  simp only [weight, compactCycleWeight, exactListRead]",
        "  rw [show 8 - 1 = 7 from rfl, descent_snapshot]",
        f"  have hh : {seed_literal} = List.map Int.toNat ({seed_literal} : List ℤ) := rfl",
        "  rw [hh, List.getElem?_map]",
        f"  cases (({seed_literal} : List ℤ)[j]?) <;> rfl",
        "def stepOK (n i : ℕ) : Bool :=",
        "  decide (exactListRead (row (n+1)) i = shortExactStep 8 n weight (row n) (row (n+1-8)) i)",
        "def pointOK (n i : ℕ) : Bool :=",
        "  halfAxisPointOK ((row n).map Int.ofNat) ((row (n+1)).map Int.ofNat) i (bracket n i)",
        "def joinOK (n i : ℕ) : Bool :=",
        "  (bracket n i).upper.less (bracket n (i+1)).lower",
        f"def lengthOK (n : ℕ) : Bool := decide ((row n).length ≤ {WIDTH})",
        "def centerOK (n : ℕ) : Bool := halfAxisCenterOK n ((row (n+1)).map Int.ofNat)",
    ]
    output(directory / "FiniteCutoffEightData.lean", modules, lines)
    return modules


def sign_parts(n):
    # Keep each process within the measured worst-size batch. Grouping is
    # aligned with the individual Bool proof boundaries.
    group_size = HORNERS_PER_LEAF * max(1, 8000 // ((n-1)*HORNERS_PER_LEAF))
    return list(chunks(0, (n - 2) // 2, group_size))


def write_leaves(directory, begin, stop, *, signs):
    modules = []
    for n in range(begin, stop):
        if signs:
            for part, (start, end) in enumerate(sign_parts(n)):
                module = f"FinitePoint{n:03d}Part{part}"
                lines = ["set_option maxHeartbeats 0"]
                for a,b in chunks(start, end, HORNERS_PER_LEAF):
                    lines.append(
                        f"theorem point{n}_{a} : arithmeticBlockOK (pointOK {n}) {a} {b-a} = true := by decide")
                if part == 0:
                    lines.extend([
                        f"theorem join{n} : arithmeticBlockOK (joinOK {n}) 0 {(n-2)//2-1} = true := by decide",
                        f"theorem center{n} : centerOK {n} = true := by decide",
                    ])
                output(directory / (module + ".lean"), ["FiniteCutoffEightData"], lines)
                modules.append(module)
        else:
            module = f"FiniteStep{n:03d}"
            lines = ["set_option maxHeartbeats 0"]
            for a,b in chunks(0, WIDTH, CELLS_PER_LEAF):
                lines.append(
                    f"theorem step{n}_{a} : arithmeticBlockOK (stepOK {n}) {a} {b-a} = true := by decide")
            lines.append(f"theorem length{n+1} : lengthOK {n+1} = true := by decide")
            output(directory / (module + ".lean"), ["FiniteCutoffEightData"], lines)
            modules.append(module)
    return modules


def decide_tree(entries, var, leaf, depth=1):
    indent = "  " * depth
    if len(entries) == 1:
        a, b = entries[0]
        return [indent + statement for statement in leaf(a, b)]
    mid = len(entries) // 2
    cut = entries[mid][0]
    return (
        [indent + f"by_cases h{cut} : {var} < {cut}"]
        + add_case(decide_tree(entries[:mid], var, leaf, depth + 1), depth)
        + add_case(decide_tree(entries[mid:], var, leaf, depth + 1), depth)
    )


def add_case(lines, depth):
    return ["  " * depth + "· " + lines[0].lstrip()] + lines[1:]


def write_joins(directory, first, stop, *, signs):
    modules = []
    group_width = HORNERS_PER_LEAF if signs else CELLS_PER_LEAF
    base = "point" if signs else "step"
    for n in range(first, stop):
        module = f"Finite{base.title()}Join{n:03d}"
        numerical = []
        reach = (n - 2) // 2 if signs else WIDTH
        numerical = [
            f"private theorem read_{n} (i : ℕ) (hi : i < {reach}) : {base}OK {n} i = true := by",
            *decide_tree(list(chunks(0, reach, group_width)), "i",
                lambda a,b: [f"exact arithmeticBlock_read {base}{n}_{a} (by omega) (by omega)"]),
        ]
        if signs:
            numerical.extend([
                f"theorem windows_{n} : halfAxisDyadicOK {n} ((row {n}).map Int.ofNat)",
                f"    ((row {n+1}).map Int.ofNat) (fun i => bracket {n} i) = true := by",
                f"  apply halfAxisDyadicOK_of_split",
                f"  · exact fun i => read_{n} i.val i.isLt",
                f"  · intro i",
                f"    exact arithmeticBlock_read join{n} (Nat.zero_le i.val) i.isLt",
                f"  · exact center{n}",
            ])
        else:
            numerical.extend([
                f"theorem insertion_{n} (i : ℕ) (hi : i < {WIDTH}) :",
                f"    exactListRead (row {n+1}) i =",
                f"      exactListStep 8 {n} (compactCycleWeight 8) (row {n}) (row {n+1-8}) i := by",
                f"  rw [← weight_eq, ← shortExactStep_eq]",
                f"  · exact of_decide_eq_true (read_{n} i hi)",
                f"  · intro j hj",
                f"    rw [weight_eq]",
                f"    exact compactCycleWeight_support 8 j (by decide) hj",
            ])
        dependencies = ([f"FinitePoint{n:03d}Part{part}" for part in range(len(sign_parts(n)))]
                        if signs else [f"FiniteStep{n:03d}"])
        output(directory / (module + ".lean"), dependencies, numerical)
        modules.append(module)
    return modules


def write_final(directory, step_joins, point_joins):
    lines = [
        f"private theorem seed : ∀ i < {WIDTH}, exactListRead (row 8) i = compactCycleWeight 8 i := by",
        "  intro i hi",
        "  rw [← weight_eq]",
        "  rfl",
        f"private theorem short : ∀ n < 8, ∀ i < {WIDTH}, exactListRead (row n) i = 0 := by",
        "  intro n hn i _",
        "  simp [row, hn, exactListRead]",
        f"private theorem steps (n : ℕ) (hlo : 8 ≤ n) (hhi : n < {END}) (i : ℕ) (hi : i < {WIDTH}) :",
        "    exactListRead (row (n+1)) i =",
        "      exactListStep 8 n (compactCycleWeight 8) (row n) (row (n+1-8)) i := by",
        *decide_tree(list(chunks(8, END, 1)), "n", lambda a,b: [
            f"have h : n = {a} := by omega", "subst n", f"exact insertion_{a} i hi"]),
        f"private theorem lengths (n : ℕ) (hhi : n ≤ {END}) : (row n).length ≤ {WIDTH} := by",
        "  by_cases hs : n ≤ 8",
        "  · interval_cases n <;> decide",
        *add_case(decide_tree(list(chunks(9, END+1, 1)), "n", lambda a,b: [
            f"have h : n = {a} := by omega", "subst n", f"exact of_decide_eq_true length{a}"], 2), 1),
        f"private theorem windows (n : ℕ) (hlo : 32 ≤ n) (hhi : n < {END}) :",
        "    halfAxisDyadicOK n ((row n).map Int.ofNat) ((row (n+1)).map Int.ofNat)",
        "      (fun i => bracket n i) = true := by",
        *decide_tree(list(chunks(BEGIN, END, 1)), "n", lambda a,b: [
            f"have h : n = {a} := by omega", "subst n", f"exact windows_{a}"]),
        "",
        "open LongCycles Polynomial in",
        f"theorem original_strict_and_weak_cutoff8_sizes32_{END-1} :",
        f"    ∀ n : ℕ, 32 ≤ n → n ≤ {END-1} →",
        "      StrictNegativeInterlacing (enumerator n 8).divX (enumerator (n+1) 8).divX (n-2) ∧",
        "        WeakRealInterlacing (enumerator n 8) (enumerator (n+1) 8) := by",
        "  intro n hn htop",
        "  exact original_strict_and_weak_block_of_checked_half_axis (k := 8) (first := 32)",
        f"    (last := {END}) (width := {WIDTH}) (by decide) (by decide) (by decide)",
        "    row short seed steps lengths (fun m i => bracket m i) windows n hn (by omega)",
        f"#print axioms original_strict_and_weak_cutoff8_sizes32_{END-1}",
    ]
    output(directory / "CutoffEightFinitePrefix.lean", ["HalfAxisBlock", *step_joins, *point_joins], lines)


def generate(path, archive, pilot):
    path.mkdir()
    windows = archive_windows(archive)
    rows = coefficient_rows()
    selected = {8, 242, 243, 249, 250, 251} if pilot else set(rows)
    data = write_data(path, rows, windows, selected)
    steps = write_leaves(path, 249 if pilot else 8, END, signs=False)
    signs = write_leaves(path, 249 if pilot else BEGIN, END, signs=True)
    step_joins = write_joins(path, 249 if pilot else 8, END, signs=False)
    point_joins = write_joins(path, 249 if pilot else BEGIN, END, signs=True)
    if not pilot:
        write_final(path, step_joins, point_joins)
    print(json.dumps({"data": data, "step": steps, "signs": signs,
                      "stepJoin": step_joins, "pointJoin": point_joins}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("archive", type=Path)
    parser.add_argument("--pilot", action="store_true")
    parser.add_argument("--through", type=int, default=250)
    args = parser.parse_args()
    if not 32 <= args.through <= 250 or args.pilot and args.through != 250:
        parser.error("choose a final old size in 32..250, or the largest-size pilot")
    END = args.through + 1
    WIDTH = END - 1
    generate(args.output, args.archive, args.pilot)
