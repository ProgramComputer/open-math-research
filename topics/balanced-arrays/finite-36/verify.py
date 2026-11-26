"""Reconcile all 36-row cases, with exact Sturm and independent dyadic signs."""
import argparse
from collections import Counter
import json
from math import comb, isqrt
from pathlib import Path
from subprocess import check_output
import sys

HERE = Path(__file__).resolve().parent
TOPIC = HERE.parent
N = 36
INHERITED_CASES = {(3, 5), (4, 6), (5, 7), (7, 9), (9, 11)}
DEFECT_CASES = {(7, 11), (8, 11), (8, 12), (9, 12), (10, 12)}
BUCKET_CASES = {(5, 12), (6, 12), (7, 12)}


def load_exact_vectors():
    result = {}

    def add(r, d, coeffs, source):
        key = r, d
        if key in result or len(coeffs) != N*r//d+1 or min(coeffs) <= 0 or coeffs[0] != 1:
            raise ArithmeticError(("invalid or duplicate exact vector", key))
        result[key] = coeffs, source

    for row in map(json.loads, (HERE/"inherited-vectors.jsonl").read_text().splitlines()):
        key = row["r"], row["d"]
        if key in INHERITED_CASES:
            expected = "inherited corank-two vector"
        elif key in DEFECT_CASES:
            expected = "PR 121 exact defect vector"
        else:
            raise ArithmeticError(("unexpected inherited key", key))
        if row["n"] != N or row["source"] != expected:
            raise ArithmeticError(("invalid inherited source record", key))
        add(*key, row["coefficients"], expected)
    if set(result) != INHERITED_CASES | DEFECT_CASES:
        raise ArithmeticError("incomplete inherited snapshot")
    for row in map(json.loads, (HERE/"exact-vectors.jsonl").read_text().splitlines()):
        key = row["r"], row["d"]
        expected = "bucketwise column DP" if key in BUCKET_CASES else "earlier partial replay"
        if row["n"] != N or row["source"] != expected:
            raise ArithmeticError(("invalid new source record", key))
        add(*key, row["coefficients"], expected)
    return result


def classification(r, d):
    if r == 1:
        return "rank-one theorem"
    if r == d:
        return "full-cap theorem"
    if r == d-1:
        return "corank-one theorem"
    if (r,d) == (2,4):
        return "four-column cap-two theorem"
    if N*r//d <= 14:
        return "degree-at-most-14 theorem"
    for k in range(1, N*r//d):
        lhs = ((k+1)*(N-k+1))**d
        rhs = (k*(N-k))**d
        if lhs <= 4*rhs:
            return None
    return "orientation separation"


def sign_numerator(coefficients, a, shift):
    result = coefficients[-1]
    for i, c in enumerate(reversed(coefficients[:-1]),1):
        result = -a*result + (c << (shift*i))
    return result


def dyadic_sign_check(coefficients):
    degree = len(coefficients)-1
    shift = 144
    nodes = [isqrt((coefficients[k-1] << (2*shift))//coefficients[k+1])
             for k in range(1,degree)]
    if nodes[0] <= 0 or any(a >= b for a,b in zip(nodes,nodes[1:])):
        raise ArithmeticError("dyadic nodes are out of order")
    if any((-1)**k * sign_numerator(coefficients, a, shift) <= 0
           for k,a in enumerate(nodes,1)):
        raise ArithmeticError("dyadic signs do not alternate")
    return nodes


def coefficient_sources(vectors, engine, recount_defect):
    sys.path.insert(0, str(TOPIC/"code"))
    from verify_corank_two_symbol import corank_two_count

    if recount_defect:
        from defect_histogram import coefficient as defect_count

    corank_entries = cpp_entries = defect_entries = 0
    for (r,d), (coefficients, source) in sorted(vectors.items()):
        if d-r == 2:
            replay = [corank_two_count(N,k,d) for k in range(len(coefficients))]
            if replay != coefficients:
                raise ArithmeticError(("corank-two recount differs",r,d))
            corank_entries += len(coefficients)
        if recount_defect and source == "PR 121 exact defect vector":
            for k, expected in enumerate(coefficients):
                lower, upper, _ = defect_count(N,d,r,k)
                if lower != expected or upper != expected:
                    raise ArithmeticError(("defect recount differs",r,d,k))
            defect_entries += len(coefficients)
        if engine is not None and r <= 7 and source in ("earlier partial replay", "bucketwise column DP"):
            replay = [json.loads(l)["coefficient"] for l in check_output(
                [str(engine.resolve()),str(N),str(d),str(r)], text=True).splitlines()]
            if replay != coefficients:
                raise ArithmeticError(("bucketwise recount differs",r,d))
            cpp_entries += len(coefficients)
    if corank_entries == 0:
        raise ArithmeticError("missing corank-two cases")
    print("recounted coefficients", {"corank_two":corank_entries, "bucketwise":cpp_entries, "defect":defect_entries})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dyadic-only", action="store_true")
    parser.add_argument("--write-ledger", action="store_true")
    parser.add_argument("--engine", type=Path, help="optional GMP bucketwise recount")
    parser.add_argument("--recount-defect", action="store_true", help="replay prior inclusion-exclusion counts")
    args = parser.parse_args()

    if args.dyadic_only and (args.engine is not None or args.recount_defect):
        parser.error("coefficient recounts require the full replay")
    if not args.dyadic_only:
        sys.path.insert(0, str(HERE.parents[2]/"shared/python"))
        from roots import root_report

    rows = []
    method_counts = Counter()
    vectors = load_exact_vectors()
    needed = set()
    roots = 0
    for d in range(2, N):
        for r in range(1, d+1):
            how = classification(r,d)
            degree = N*r//d
            row = dict(n=N,r=r,d=d,degree=degree)
            if how is None:
                key = r,d
                needed.add(key)
                coefficients, how = vectors[key]
                if not args.dyadic_only:
                    report = root_report(coefficients)
                    if report["distinct_real_roots"] != degree or report["squarefree_degree"] != degree:
                        raise ArithmeticError(("Sturm fails", key))
                dyadic_sign_check(coefficients)
                roots += degree
            row["method"] = how
            rows.append(row)
            method_counts[how] += 1
    if len(rows) != 629 or set(vectors) != needed or len(vectors) != 28:
        raise ArithmeticError("finite coverage or residual key discrepancy")
    if (N+1)**(2*N) <= 4*N**(2*N):
        raise ArithmeticError("infinite dimension tail separation fails")
    rows.append({"n":N,"d_min":N,"method":"orientation separation for all caps"})
    rows.append({"n":N,"d":1,"method":"binomial power, root -1 of multiplicity 36"})

    serialized = "".join(json.dumps(row,separators=(",",":"))+"\n" for row in rows)
    ledger = HERE/"coverage.jsonl"
    if args.write_ledger:
        ledger.write_text(serialized)
    elif ledger.read_text() != serialized:
        raise ArithmeticError("coverage ledger mismatch")
    if not args.dyadic_only:
        coefficient_sources(vectors, args.engine, args.recount_defect)
    print("finite cases", len(rows)-2, dict(method_counts))
    print("exact cases", len(vectors), "simple negative roots", roots)
    print("verified all d >= 36 and d = 1")


if __name__ == "__main__":
    main()
