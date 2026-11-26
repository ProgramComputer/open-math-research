# Open Problems in Mathematics

Reviewed proofs, disproofs, and partial theorems on established open problems. Select a result to read its statement, argument, and verification record. Rows are ranked by mathematical significance.

| Result | Outcome | Formal verification |
|---|---|---|
| [A prism-slice split can destroy interlacing](topics/prism-splitting/README.md) | Disproof by an infinite family | 🟩 Full · Lean 4<br>🟩 Full · Rocq |
| [Real-rootedness and interlacing for strict peaks in Catalan words](topics/catalan-word-peaks/README.md) | Proof for every word length | 🟩 Full · Lean 4 |
| [Eventual simple negative zeros for balanced arrays in every dimension](topics/balanced-arrays/eventual-all/README.md) | One eventual row threshold works for every dimension $d\ge2$ and every cap | 🟨 Partial · Lean 4 (support, degree and sign reduction) |
| [Sharp coefficient thresholds for counting polynomial zeros in disks](topics/balanced-arrays/root-distributions/single-sign/README.md) | Sharp angular thresholds and disk-count bounds independent of degree, with optimal order at weak curvature | ⬜ None |
| [Binomial normalization for weighted binary matrices](topics/balanced-arrays/weighted-normalization/README.md) | Partial theorem for arbitrary cell weights and row intervals, giving an explicit real-rootedness range | ⬜ None |
| [Sharp likelihood bounds for the size of a marked row](topics/balanced-arrays/marked-row-likelihood/README.md) | Partial theorem for weighted arrays with prescribed column sums, with sharp binomial odds under row exchangeability | 🟨 Partial · Lean 4 (pairings and overlap counts) |
| [Explicit dimension bounds for every balanced-array row cap](topics/balanced-arrays/effective-sublinear/README.md) | Simple negative zeros above explicit thresholds for $d\ge n^{99/100}$ or $d\ge100n/\log n$, with respective height cutoffs | ⬜ None |
| [Effective high-cap sectors for balanced arrays](topics/balanced-arrays/effective-sectors/README.md) | Every height when $4d\ge n$ and $10r\ge9d$, plus near-full caps at explicit square-root dimension $`d^2\ge16384n\log(n+1)`$ | ⬜ None |
| [Simple negative zeros for four balanced columns with row cap two](topics/balanced-arrays/four-columns/README.md) | Proof for every row count | ⬜ None |
| [Ribbon Schur positivity for balanced arrays](topics/balanced-arrays/koszul-ribbons/README.md) | Partial theorem giving strong Koszulness and positivity for every ribbon specialization | ⬜ None |
| [An effective sparse-rank bound for balanced arrays](topics/balanced-arrays/sparse-rank-curvature/README.md) | Partial theorem giving all simple negative zeros under a factor-four criterion with effective rank $r-\sqrt{r\log r}/8$ | ⬜ None |
| [Fixed balanced-array minors and positivity through 18 cells](topics/balanced-arrays/fixed-shapes/README.md) | Exact decision for each skew shape and universal binomial-basis positivity through 18 cells at unit weights | ⬜ None |
| [Simple negative zeros for balanced arrays in growing dimensions](topics/balanced-arrays/dense-regime/README.md) | All roots for $d\ge Cn/\log n$ at large $n$ and in a rank-dependent range, plus all 508,000 simple negative roots in one million-row instance | ⬜ None |
| [Root distributions of balanced binary arrays](topics/balanced-arrays/root-distributions/README.md) | Finite disk counts and five limiting laws, including the uniform law for growing sparse caps | ⬜ None |
| [Excedance zeros for permutations with long cycles](topics/long-cycle-excedances/README.md) | Strict consecutive interlacing for $k\ge7$ and $n/k\ge20$ at every size, through old size 250, from old size 10,000 onward, for $n\le4k-1$, and at every size for $k=3$ | ⬜ None |
| [Zeros of ordered partitions counted by large blocks](topics/ordered-large-blocks/README.md) | All sizes for thresholds two through four, strict eventual interlacing at each fixed threshold, and a positive proportion of the roots when both threshold and size-to-threshold ratio grow | 🟨 Partial · Lean 4 |
| [Eventual real-rootedness of the Eulerian matrix square](topics/eulerian-matrix-square/README.md) | Partial theorem covering every sufficiently large row | 🟨 Partial · Lean 4 |
| [Real zeros of balanced binary arrays](topics/balanced-arrays/README.md) | Real-rootedness and strict consecutive interlacing at every row count for $r=d-1$ | 🟨 Partial · Lean 4 (labeled-array coefficient formula) |
| [Ordinary descents of permutations with long cycles](topics/long-cycle-descents/README.md) | Repository partial theorem for single cycles and large-cutoff cycle-type mixtures | ⬜ None |
| [Ribbon matroids have the Narayana polynomial](topics/ribbon-matroids/README.md) | Proof of the identity and simple negative roots for every nonempty connected ribbon | 🟩 Full · Lean 4 |

**Lean or Rocq key**　🟩 Full (entire statement) · 🟨 Partial (named components) · ⬜ None (no checked proof)

[Stable Lean audit and verification records](shared/lean/publication/README.md)

## Partial work

- A [linear dimension bound for every row cap](topics/balanced-arrays/adjacent-quotas/README.md) gives simple negative zeros when $200d\ge59n$ at the lower height $n\ge10^{200}$.
- Earlier balanced-array bounds: [five-thirds row bound and polynomial cap or corank range](topics/balanced-arrays/fifth-thirds/README.md), [all fixed quadratic aspects](topics/balanced-arrays/critical-aspect/README.md), [absolute quadratic cutoff](topics/balanced-arrays/quadratic/README.md), [quartic-log cutoff](topics/balanced-arrays/very-tall/README.md), and [dimension-uniform fixed-cap threshold](topics/balanced-arrays/fixed-cap/README.md).
- [Balanced arrays](topics/balanced-arrays/README.md) with row cap $r=d-1$ have simple negative zeros and strictly alternate at every row count. Lean proves its inclusion–exclusion formula from the labeled arrays. The general conjecture also holds in [every degree through fourteen](topics/balanced-arrays/low-degree.md) and for every rank and dimension through 24 rows. For four columns with row cap two, several singleton slices and the sum of the two- and four-singleton slices strictly interlace across consecutive rows.
- Every sufficiently large [Eulerian-square row](topics/eulerian-matrix-square/README.md) has only simple real roots. At every row from $n=3$, the two extreme roots at each end strictly alternate with the next row. The all-root cutoff is unknown.
- For [long-cycle excedances](topics/long-cycle-excedances/README.md), any remaining counterexample has old size $251\le n<10{,}000$ with $4\le n/k<20$ among thresholds $k\ge7$. Bowen Zuo reports separate all-size proofs for $k=4,5,6$. Repository verification of those claims is pending. [Zuo’s release](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/releases/tag/v1.2.0)
- Bowen Zuo proved Alexandersson’s ordinary-descent conjecture for every minimum cycle length. The repository’s earlier partial theorem also covers arbitrary allowed cycle-type mixtures in its large-cutoff range. [Long-cycle descents](topics/long-cycle-descents/README.md)

## Citation

```bibtex
@misc{ProgramComputerOpenMathResearch2026,
  author       = {{ProgramComputer}},
  title        = {{Open Problems in Mathematics}},
  year         = {2026},
  howpublished = {GitHub repository},
  url          = {https://github.com/ProgramComputer/open-math-research}
}
```

## License

Copyright 2026 ProgramComputer. [ISC License](LICENSE).
