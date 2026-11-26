# Balanced arrays through 36 rows

For every $0\le n\le36$, every $d\ge2$ and every $1\le r\le d$, the polynomial counting labeled binary $n$-by-$d$ arrays with row sizes at most $r$, by their common column sum, has all $\lfloor nr/d\rfloor$ zeros simple and negative. A constant has no roots. When $d=1$ the polynomial is $(1+q)^n$, with root $-1$ of multiplicity $n$ for $n>0$. This package completes the row $n=36$. The [earlier finite package](../finite-residual/README.md) proves the result through $n=35$. **⬜ None** for Lean or Rocq. [Alexandersson’s conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

## Complete coverage at 36 rows

There are 629 pairs $(r,d)$ with $2\le d<36$ and $1\le r\le d$. The [coverage ledger](coverage.jsonl) gives each pair exactly one proof method in the following precedence order.

| Method | Cases |
| --- | ---: |
| Rank one | 34 |
| Full cap | 34 |
| Corank one | 33 |
| Four columns and cap two | 1 |
| Degree at most fourteen | 211 |
| Exact orientation separation | 288 |
| Exact vectors, with Sturm and dyadic signs | 28 |

The first three rows use the [rank-one and full-cap criteria](../finite-linear-reduction.md) and the [corank-one theorem](../no-full-row.md). The next two use the [four-column theorem](../four-columns/README.md) and the [degree bound theorem](../low-degree.md). For orientation separation the verifier tests, at each internal quota $k$,
$$
\big((k+1)(36-k+1)\big)^d>4\big(k(36-k)\big)^d.
$$
The [orientation comparison](../orientation-normalization.md) lower-bounds the actual coefficient ratio by the ratio in this test, and the strict separation criterion then gives simple negative zeros. For every $d\ge36$ and each cap, the lower bound is at least $(1+1/36)^{72}>4$. The verifier checks the last strict inequality by integer powers. The ledger includes a single analytic tail record for these infinitely many dimensions.

## Exact residual cases

The 28 distinct residual polynomials account for 617 simple negative roots. The [new exact archive](exact-vectors.jsonl) contains 18 vectors: 15 from the earlier incomplete 36-row replay and three newly finished by the bucketwise column transfer. Five older corank-two vectors and the five vectors from [PR #121](https://github.com/ProgramComputer/open-math-research/pull/121) are read directly from their respective archives.

| Source | Cases $(r,d)$ |
| --- | --- |
| [Existing column-extension archive](../results/column-extension-corank-two.jsonl.gz) | $(3,5),(4,6),(5,7),(7,9),(9,11)$ |
| Earlier partial replay | $(3,6),(3,7),(4,7),(4,8),(5,8),(6,8),(4,9),(5,9),(6,9),(5,10),(6,10),(7,10),(8,10),(5,11),(6,11)$ |
| [Defect-histogram package](../curvature-compensation/README.md) | $(7,11),(8,11),(8,12),(9,12),(10,12)$ |
| New bucketwise column counts | $(5,12),(6,12),(7,12)$ |

Every vector has positive coefficients, leading degree $D=\lfloor36r/d\rfloor$ and constant coefficient one. Exact rational Sturm chains give $D$ distinct real roots. The second check uses integer arithmetic only. At each internal quota $k$, it tests the sign at the negative dyadic of magnitude $2^{-144}\lfloor2^{144}\sqrt{a_{k-1}/a_{k+1}}\rfloor$. The magnitudes strictly increase and the signs alternate. With the signs at zero and negative infinity, this gives $D$ disjoint open intervals with a root in each. Both arguments certify simplicity and negativity. An [independent audit](independent-review.md) also matched the residual selection and source vectors, recounted quotas one and two and checked positive definite Bézout matrices for every exact case.

## Counting and replay

The GMP [bucketwise counter](count.cpp) builds one column at a time, processing its row-capacity buckets in increasing order. Choosing $b$ out of $h$ rows in the current bucket has multiplicity $\binom hb$. These rows move to the preceding bucket, which has already been processed, and equal intermediate histograms are combined. In the clipped build, before a column with $c$ columns still to fill, a capacity above $c$ is equivalent to $c$. In the top bucket of capacity $c$, selected and unselected rows both move to capacity $c-1$ after the column. Insufficient capacity for the remaining entries rules out a state. In the comparison build, the state keeps the actual row loads and processes buckets in decreasing order. Both retain the number of rows selected so far in each column.

From the repository root:

~~~sh
python3 -B topics/balanced-arrays/finite-36/verify.py --dyadic-only
python3 -B topics/balanced-arrays/finite-36/verify.py
~~~

The first command uses the standard library and the second needs python-flint 0.9.0 for the Sturm checks and inclusion–exclusion recount of the eight exact corank-two cases. The defect package supplies its own [independent checks](../curvature-compensation/independent-review.md).

To recount the 17 newly archived vectors of cap at most seven, compile the bucketwise counter and pass it to the full check. The remaining new vector, $(r,d)=(8,10)$, is independently recounted by the corank-two inclusion–exclusion formula in the ordinary full check.

~~~sh
c++ -DCLIPPED -std=c++17 -O3 topics/balanced-arrays/finite-36/count.cpp $(pkg-config --cflags --libs gmpxx) -o /tmp/balanced-36-bucket
python3 -B topics/balanced-arrays/finite-36/verify.py --engine /tmp/balanced-36-bucket
~~~
