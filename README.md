# Open Problems in Mathematics

Reviewed proofs, disproofs, and partial theorems on established open problems. Select a result to read its statement, argument, and verification record. Rows are ranked by mathematical significance.

| Result | Outcome | Formal verification |
|---|---|---|
| [A prism-slice split can destroy interlacing](topics/prism-splitting/README.md) | Disproof by an infinite family | 🟩 Full · Lean 4<br>🟩 Full · Rocq |
| [Zeros of ordered partitions counted by large blocks](topics/ordered-large-blocks/README.md) | Strict interlacing at every fixed threshold for sufficiently large rows, and at every size for thresholds two through four | 🟨 Partial · Lean 4 |
| [Eventual real-rootedness of the Eulerian matrix square](topics/eulerian-matrix-square/README.md) | Partial theorem covering every sufficiently large row | 🟨 Partial · Lean 4 |
| [Real zeros of balanced binary arrays](topics/balanced-arrays/README.md) | Partial theorems, including the closest zero in every nonconstant row with $d\ge2$ | 🟨 Partial · Lean 4 |
| [Ordinary descents of permutations with long cycles](topics/long-cycle-descents/README.md) | Partial theorem, including every single cycle | ⬜ None |
| [Ribbon matroids have the Narayana polynomial](topics/ribbon-matroids/README.md) | Proof | 🟨 Partial · Lean 4 |
| [Largest real zero for strict peaks in Catalan words](topics/catalan-word-peaks/README.md) | Partial theorem for every length from three, with a zero-free interval at every length | ⬜ None |

**Lean or Rocq key**　🟩 Full (entire statement) · 🟨 Partial (named components) · ⬜ None (no checked proof)

## Partial work

- For [balanced arrays](topics/balanced-arrays/README.md), the conjecture holds in [every degree through fourteen](topics/balanced-arrays/low-degree.md) and for every rank and dimension through 24 rows. For arbitrary row counts, $d\ge(n+1)\log(2)/2$ suffices.
- Every sufficiently large [Eulerian-square row](topics/eulerian-matrix-square/README.md) has only simple real roots. At every row from $n=3$, the two extreme roots at each end strictly alternate with the next row. The all-root cutoff is unknown.
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
