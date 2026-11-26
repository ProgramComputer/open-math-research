"""Finite checks of normalized matching and the numerical curvature bounds."""
import argparse
from collections import defaultdict, deque
from fractions import Fraction
import gzip
import itertools
import json
from pathlib import Path
from runpy import run_path


HERE = Path(__file__).resolve().parent
COUNTS = run_path(str(HERE.parent / "code/coefficients.py"))


def row_options(weights, lo, hi):
    for mask in range(1 << len(weights)):
        if lo <= mask.bit_count() <= hi:
            weight = 1
            for j, value in enumerate(weights):
                if mask & (1 << j):
                    weight *= value
            if weight:
                yield mask, weight


def fibers(weights, intervals):
    """Direct enumeration, keeping the marked row and every column margin."""
    d = len(weights[0])
    options = [list(row_options(row, *bounds)) for row, bounds in zip(weights, intervals)]
    result = defaultdict(lambda: defaultdict(int))
    for rows in itertools.product(*options):
        quotas = [0] * d
        weight = 1
        for mask, factor in rows:
            weight *= factor
            for j in range(d):
                quotas[j] += (mask >> j) & 1
        result[tuple(quotas)][rows[0][0]] += weight
    return result


def check_coupling(lower, upper):
    """A saturated integer flow is a coupling after normalization."""
    low_total, high_total = sum(lower.values()), sum(upper.values())
    target = low_total * high_total
    source, sink = -1, -2
    graph = defaultdict(dict)

    def edge(u, v, amount):
        graph[u][v] = amount
        graph[v][u] = 0

    for mask, mass in lower.items():
        edge(source, mask, mass * high_total)
        for child in upper:
            if mask & child == mask:
                edge(mask, child, target)
    for mask, mass in upper.items():
        edge(mask, sink, mass * low_total)
    routed = 0
    while routed < target:
        queue = deque([source])
        parent = {source: source}
        while queue and sink not in parent:
            u = queue.popleft()
            for v, capacity in graph[u].items():
                if capacity > 0 and v not in parent:
                    parent[v] = u
                    queue.append(v)
        assert sink in parent, (lower, upper, routed, target)
        path = []
        v = sink
        while v != source:
            u = parent[v]
            path.append((u, v))
            v = u
        delta = min(graph[u][v] for u, v in path)
        for u, v in path:
            graph[u][v] -= delta
            graph[v][u] += delta
        routed += delta
    return routed


def check_size_comparisons(profiles, n, d):
    """Cross-multiply the proposed tilted inequality for every ordered size pair."""
    count = 0
    for quotas, profile in profiles.items():
        larger = tuple(q+1 for q in quotas)
        if larger not in profiles:
            continue
        bound = max(1, max(min(q, n-q-1) for q in quotas))
        first = [0] * (d+1)
        second = [0] * (d+1)
        for mask, weight in profile.items():
            first[mask.bit_count()] += weight
        for mask, weight in profiles[larger].items():
            second[mask.bit_count()] += weight
        for s in range(d):
            for t in range(s+1,d+1):
                left = first[s] * second[t]
                right = first[t] * second[s]
                if left or right:
                    assert left * bound**(t-s) >= right * (bound+1)**(t-s)
                    count += 1
    return count


def matching_records():
    cases = [
        ([[1]*4]*3, [(0,4),(0,2),(0,2)]),
        ([[2,1,3,1],[1,3,1,0],[2,1,1,3],[1,2,3,1]], [(0,4),(1,3),(0,3),(2,2)]),
        ([[1]*6]*3, [(0,6),(0,3),(0,3)]),
        ([[0,2,1,2,1,1],[1,3,2,1,2,1],[2,1,0,1,1,2]], [(0,6),(1,3),(2,3)]),
        ([[1]*6]*3, [(0,6),(0,4),(0,5)]),
        ([[2,1,3,1,2,1],[1,2,1,0,3,1],[1,3,1,2,1,2]], [(0,6),(1,5),(2,4)]),
    ]
    result = []
    for weights, intervals in cases:
        rows = []
        d = len(weights[0])
        profiles = fibers(weights, intervals)
        size_comparisons = check_size_comparisons(profiles, len(weights), d)
        small_caps = all(hi <= 3 for _, hi in intervals[1:])
        for quotas, profile in sorted(profiles.items()):
            layers = [dict() for _ in range(d+1)]
            for mask, value in profile.items():
                layers[mask.bit_count()][mask] = value
            checked = []
            for j, (lo, hi) in enumerate(zip(layers, layers[1:])):
                if small_caps and lo and hi:
                    check_coupling(lo, hi)
                    checked.append(j)
            rows.append([quotas, sorted(profile.items()), checked])
        result.append(dict(weights=weights, row_intervals=intervals,
                           size_comparisons=size_comparisons, fibers=rows))
    return result


def coefficient_records():
    result = []
    for n in range(2, 13):
        for r in range(2, 8):
            for d in range(r+1, 9):
                degree = n*r//d
                values = [COUNTS["column_count"](n,k,r,d) for k in range(degree+1)]
                assert values == [COUNTS["row_count"](n,k,r,d) for k in range(degree+1)]
                floor = 1+Fraction(d, d+n*(r-1))
                for k in range(1, degree):
                    y = Fraction(d*(k-1), n)
                    e = (d-r)*max(Fraction(0), y-r+1)/(d-y)
                    sharper = (1+Fraction(1,k))*(1+Fraction(1,n-k))*(1+e/k)
                    actual = Fraction(values[k]**2, values[k-1]*values[k+1])
                    assert actual >= sharper**d >= floor**d
                result.append([n,r,d,values])
    return result


def monomial_records():
    """Compare coefficients before choosing numerical cell weights."""
    n = d = 3
    answer = []
    for other_intervals in (((0,2),(0,2)), ((1,3),(2,2))):
        tables = defaultdict(list)
        options = [row_options([1]*d,*bounds) for bounds in ((0,d),*other_intervals)]
        for rows in itertools.product(*options):
            masks = tuple(mask for mask,_ in rows)
            quotas = tuple(sum((mask>>j)&1 for mask in masks) for j in range(d))
            cells = sum(mask<<(d*i) for i,mask in enumerate(masks))
            tables[quotas].append((cells,masks[0].bit_count()))
        records = []
        for quotas, red in sorted(tables.items()):
            blue = tables.get(tuple(q+1 for q in quotas), ())
            buckets = defaultdict(lambda: [0,0])
            for a,i in red:
                for b,j in blue:
                    if i == j:
                        continue
                    key = (min(i,j),max(i,j),a&b,a^b)
                    buckets[key][int(i>j)] += 1
            bound = max(1,max(min(q,n-q-1) for q in quotas))
            for (s,t,common,exclusive),(target,source) in sorted(buckets.items()):
                assert target*bound**(t-s) >= source*(bound+1)**(t-s)
                records.append([quotas,s,t,common,exclusive,target,source])
        answer.append(dict(other_intervals=other_intervals, coefficients=records))
    return answer


def examples():
    for n,r,d in ((10000,2,130),(10000,3,190),(10000,4,220),(10000,12,395)):
        new = (1+Fraction(d,d+n*(r-1)))**d
        k = min(n//2,n*r//d-1)
        old = ((1+Fraction(1,k))*(1+Fraction(1,n-k)))**d
        assert old < 4 < new
        print(f"n={n}, r={r}, d={d}: unrestricted floor < 4 < new uniform floor.")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--record", action="store_true")
    args = parser.parse_args()
    matching = matching_records()
    coefficients = coefficient_records()
    monomials = monomial_records()
    record = {"matching": matching, "coefficient_vectors": coefficients, "monomials":monomials}
    payload = json.dumps(record, separators=(",",":")).encode()
    path = HERE / "checks.json.gz"
    if args.record:
        path.write_bytes(gzip.compress(payload, mtime=0))
    else:
        assert gzip.decompress(path.read_bytes()) == payload
    num_fibers = sum(len(case["fibers"]) for case in matching)
    transitions = sum(len(j) for case in matching for _,_,j in case["fibers"])
    small_count = sum(len(case["fibers"]) for case in matching
                      if all(hi <= 3 for _,hi in case["row_intervals"][1:]))
    print(f"{transitions} exact couplings across {small_count} small-cap fibers.")
    print(f"{num_fibers} nonempty weighted fibers enumerated in total.")
    print(f"{sum(case['size_comparisons'] for case in matching)} nonzero tilted size comparisons.")
    print(f"{sum(len(case['coefficients']) for case in monomials)} coefficientwise comparisons.")
    print(f"{len(coefficients)} coefficient vectors agreed by row and column counting.")
    examples()


if __name__ == "__main__":
    main()
