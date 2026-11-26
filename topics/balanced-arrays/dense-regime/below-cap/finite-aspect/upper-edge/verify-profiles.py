"""Direct enumeration of labeled column subsets for small margin vectors."""
from fractions import Fraction as Q
from itertools import combinations, product


def run():
    cases = switches = arrays = 0
    for n,d in ((2,3),(3,3),(3,4),(4,4),(5,3)):
        choices = [list(combinations(range(n),j)) for j in range(n+1)]
        for q in range(n):
            for ell in range(d):
                sizes = [q+1]*ell + [q]*(d-ell)
                records = []
                for cols in product(*(choices[j] for j in sizes)):
                    degrees = [0]*n
                    for col in cols:
                        for i in col:
                            degrees[i] += 1
                    records.append((degrees,cols[-1]))
                arrays += len(records)
                for r in range(1,d):
                    valid = [(rows,col) for rows,col in records if max(rows)<=r]
                    if not valid:
                        continue
                    s = n*r - sum(sizes)
                    R = Q(r*(d-r),d)
                    M = Q(sum(sum(x < r for x in rows) for rows,_ in valid),len(valid))
                    A = Q(sum(sum(x < r and i not in col for i,x in enumerate(rows))
                              for rows,col in valid),len(valid))
                    pairs = Q(s*(s-1),n*(n-1))
                    delta = min(pairs/R+Q(s,n)/R+Q(2*s,n*r), (2/R+Q(2,r))*pairs)
                    baseline = Q(n*s,n+s-1)
                    assert 0 <= M-baseline <= Q(n*(n-1),n+s-1)*delta
                    average = ((d-r)*M+s)/d
                    assert 0 <= A-average <= Q(ell,d)
                    next_sizes = sizes[:-1]+[q+1]
                    # A second enumeration independently counts extensions.
                    if A:
                        next_count = 0
                        for cols in product(*(choices[j] for j in next_sizes)):
                            rows = [0]*n
                            for col in cols:
                                for i in col:
                                    rows[i] += 1
                            next_count += max(rows)<=r
                        assert len(valid)*A == (q+1)*next_count
                        switches += 1
                    cases += 1
    print(f"Checked {cases} feasible cap-margin cases, {switches} positive extension identities, {arrays} labeled arrays before imposing the cap.")


if __name__ == "__main__":
    run()
