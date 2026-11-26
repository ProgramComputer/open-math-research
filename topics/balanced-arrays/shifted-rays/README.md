# Shifted rays of capped binary arrays

Fix $n$ labeled rows, $d$ labeled columns and row cap $r$. Let $A_n(v)$ count arrays with column margin vector $v$, with value zero for infeasible margins. For each integer offset $u$ define the finite Laurent polynomial

$$
F_u(q)=\sum_{k\in\mathbb Z} A_n(k\mathbf1+u)q^k .
$$

The original [balanced-array conjecture of Per Alexandersson](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) concerns $F_0$. This experiment checks a stronger proposed invariant on all nonzero rays. It asks whether each ray is real-rooted and whether each pair $F_u,F_{u+e_i}$ lies in weak proper position in that order after common monomial clearing. For polynomials $f,g$ with positive leading coefficients and real roots, the orientation here is $f'g-fg'\ge0$ on the real line with interlacing roots, allowing equality and common roots.

## Exact experiment on actual arrays

The experiment includes every $0\le n\le8$ and $1\le r\le d$ for $2\le d\le5$. The additional ranges below are inclusive from $n=0$ to the listed maximum. A point covered by both ranges appears only once.

| $r$ | $d$ | Maximum $n$ |
| ---: | ---: | ---: |
| 2 | 4 | 20 |
| 2 | 5 | 16 |
| 3 | 5 | 16 |
| 2 | 6 | 12 |
| 3 | 6 | 12 |
| 4 | 6 | 12 |

All 80,100 nonzero rays have only real zeros. All 295,350 tested coordinate adjacencies satisfy the weak proper-position relation. These counts represent offsets up to permutation and translation by the all-ones vector, and use only one coordinate per group of equal offset values. A coordinate step with no nonzero successor is omitted.

The [deduplicated exact archive](shifted-rays.jsonl.gz) stores the row count, cap, dimension, sorted offset with minimum zero, exact coefficients in increasing quota order, and the exact Sturm report. Each edge record gives the changed coordinate index, the signed Euclidean interlacing result and the result of a separate Wronskian check. For the latter, the script computes the square-free factors of $f'g-fg'$ and uses Sturm counts to exclude odd-multiplicity real zeros, after checking the leading sign and degree parity. The zero Wronskian also passes. These are exact checks using integer or rational polynomial arithmetic.

The replay constructs counts by adding all allowed supports to each sorted margin vector, accumulating orbit totals and dividing by the orbit size. It also constructs unsorted labeled margin counts independently through four rows for every tested shape, comparing every orbit and checking support. When normalizing a successor offset by subtracting $s\mathbf1$, the corresponding ray changes by the factor $q^{-s}$. The check therefore uses $q^sF_u$ and the normalized successor, which clears the same monomial from both.

Run from the repository root with Python and python-flint.

~~~sh
python -B topics/balanced-arrays/shifted-rays/verify.py
~~~

Pass `--write-archive` to regenerate the compressed archive with a zero gzip timestamp and no stored filename.

## Limits of abstract row addition

For actual arrays, one row updates the rays by summing $F_{u-\mathbf1_S}$ over $|S|\le r$. A sector argument gives individual real-rootedness for one abstract update when the nonzero input family has consistent oriented adjacencies and shift equivariance on the relevant paths. A symmetric abstract family shows that the update can lose adjacent interlacing. A second example begins with a finite symmetric polynomial whose nonzero rays satisfy the weak oriented relation and has a nonreal equal diagonal after two ordinary capped updates. The examples concern the proposed closure mechanism. They give no counterexample among actual array counts. [Arguments and exact examples](argument.md) · [Independent review](independent-review.md)

The one-dimensional problem of imposing only total array size admits interlacing by residue classes. The [scalar comparison](scalar-residues.md) gives an elementary proof of this known consequence of Brändén’s interlacing criterion and identifies the extra difficulty of requiring equal column margins.

**⬜ None** for Lean or Rocq. [Research issue #2](https://github.com/ProgramComputer/open-math-research/issues/2)
