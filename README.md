# Open Problems in Mathematics

Reviewed proofs, disproofs, and partial theorems on established open problems. Select a result to read its statement, argument, and verification record. Rows are ranked by mathematical significance.

| Result | Outcome | Formal verification |
|---|---|---|
| [A prism-slice split can destroy interlacing](topics/prism-splitting/README.md) | Disproof by an infinite family | 🟩 Full · Lean 4<br>🟩 Full · Rocq |
| [Real-rootedness and interlacing for strict peaks in Catalan words](topics/catalan-word-peaks/README.md) | Proof for every word length | 🟨 Partial · Lean 4 |
| [Excedance zeros for permutations with long cycles](topics/long-cycle-excedances/README.md) | All rows at $k=3$, with strict interlacing at every threshold in all sufficiently large rows | ⬜ None |
| [Zeros of ordered partitions counted by large blocks](topics/ordered-large-blocks/README.md) | All sizes for thresholds two through four, strict eventual interlacing at each fixed threshold, and a positive proportion of the roots when both threshold and size-to-threshold ratio grow | 🟨 Partial · Lean 4 |
| [Eventual real-rootedness of the Eulerian matrix square](topics/eulerian-matrix-square/README.md) | Partial theorem covering every sufficiently large row | 🟨 Partial · Lean 4 |
| [Real zeros of balanced binary arrays](topics/balanced-arrays/README.md) | All row counts for $U(2,3)$, with partial theorems at general rank and dimension | 🟨 Partial · Lean 4 |
| [Ordinary descents of permutations with long cycles](topics/long-cycle-descents/README.md) | Partial theorem, including every single cycle | ⬜ None |
| [Ribbon matroids have the Narayana polynomial](topics/ribbon-matroids/README.md) | Proof | 🟨 Partial · Lean 4 |

**Lean or Rocq key**　🟩 Full (entire statement) · 🟨 Partial (named components) · ⬜ None (no checked proof)

## Partial work

- For [balanced arrays](topics/balanced-arrays/README.md), the conjecture holds in [every degree through fourteen](topics/balanced-arrays/low-degree.md) and for every rank and dimension through 24 rows. For arbitrary row counts, $d\ge(n+1)\log(2)/2$ suffices.
- Every sufficiently large [Eulerian-square row](topics/eulerian-matrix-square/README.md) has only simple real roots. At every row from $n=3$, the two extreme roots at each end strictly alternate with the next row. The all-root cutoff is unknown.
- For [long-cycle excedances](topics/long-cycle-excedances/README.md), the uniform theorem leaves a finite set of smaller rows at $k\ge4$. An explicit cutoff that permits a finite replay remains open.
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
