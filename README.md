# Open Problems in Mathematics

Reviewed proofs, disproofs, and partial theorems on established open problems. Select a result to read its statement, argument, and verification record. Rows are ranked by mathematical significance.

| Result | Outcome | Formal verification |
|---|---|---|
| [A prism-slice split can destroy interlacing](topics/prism-splitting/README.md) | Disproof by an infinite family | 🟩 Full · Lean 4<br>🟩 Full · Rocq |
| [Real-rootedness and interlacing for strict peaks in Catalan words](topics/catalan-word-peaks/README.md) | Proof for every word length | 🟩 Full · Lean 4 |
| [Simple negative zeros for four balanced columns with row cap two](topics/balanced-arrays/four-columns/README.md) | Proof for every row count | ⬜ None |
| [Simple negative zeros for balanced arrays in growing dimensions](topics/balanced-arrays/dense-regime/README.md) | All roots when $n\ge N$ and $d\ge Cn/\log n$, and all but $O(D\sqrt{n\log(n+1)}/d)$ of the $D$ roots for $2\le d\le n$ | ⬜ None |
| [Excedance zeros for permutations with long cycles](topics/long-cycle-excedances/README.md) | Strict interlacing at $k=3$ for all sizes and at every threshold for $n\ge10^{20}$ | ⬜ None |
| [Zeros of ordered partitions counted by large blocks](topics/ordered-large-blocks/README.md) | All sizes for thresholds two through four, strict eventual interlacing at each fixed threshold, and a positive proportion of the roots when both threshold and size-to-threshold ratio grow | 🟨 Partial · Lean 4 |
| [Eventual real-rootedness of the Eulerian matrix square](topics/eulerian-matrix-square/README.md) | Partial theorem covering every sufficiently large row | 🟨 Partial · Lean 4 |
| [Real zeros of balanced binary arrays](topics/balanced-arrays/README.md) | Real-rootedness and strict consecutive interlacing at every row count for $r=d-1$ | 🟨 Partial · Lean 4 (labeled-array coefficient formula) |
| [Ordinary descents of permutations with long cycles](topics/long-cycle-descents/README.md) | Partial theorem, including every single cycle | ⬜ None |
| [Ribbon matroids have the Narayana polynomial](topics/ribbon-matroids/README.md) | Proof | 🟨 Partial · Lean 4 |

**Lean or Rocq key**　🟩 Full (entire statement) · 🟨 Partial (named components) · ⬜ None (no checked proof)

[Stable Lean audit and verification records](shared/lean/publication/README.md)

## Partial work

- [Balanced arrays](topics/balanced-arrays/README.md) with row cap $r=d-1$ have simple negative zeros and strictly alternate at every row count. Lean proves its inclusion–exclusion formula from the labeled arrays. The general conjecture also holds in [every degree through fourteen](topics/balanced-arrays/low-degree.md) and for every rank and dimension through 24 rows. For four columns with row cap two, several singleton slices and the sum of the two- and four-singleton slices strictly interlace across consecutive rows.
- Every sufficiently large [Eulerian-square row](topics/eulerian-matrix-square/README.md) has only simple real roots. At every row from $n=3$, the two extreme roots at each end strictly alternate with the next row. The all-root cutoff is unknown.
- For [long-cycle excedances](topics/long-cycle-excedances/README.md), any remaining counterexample has old size $3k-1\le n<10^{20}$ and threshold $k\ge4$. Explicit bounds also settle parts of this range.
- For [long-cycle descents](topics/long-cycle-descents/README.md), the all-size question remains open at fixed minimum cycle length $k\ge3$.

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
