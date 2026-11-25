# Open Problems in Mathematics

Reviewed proofs, disproofs, and partial theorems on established open problems. Select a result to read its statement, argument, and verification record. Rows are ranked by mathematical significance.

| Result | Outcome | Formal verification |
|---|---|---|
| [A prism-slice split can destroy interlacing](topics/prism-splitting/README.md) | Disproof by an infinite family | 🟩 Full · Lean 4 |
| [Real zeros of balanced binary arrays](topics/balanced-arrays/README.md) | Partial theorems for large row or column counts | 🟨 Partial · Lean 4 |
| [Zeros of the Eulerian matrix square](topics/eulerian-matrix-square/README.md) | Partial theorem for all sufficiently large rows | 🟨 Partial · Lean 4 |
| [Ordinary descents of permutations with long cycles](topics/long-cycle-descents/README.md) | Partial theorem, including every single cycle | ⬜ None |
| [Ribbon matroids have the Narayana polynomial](topics/ribbon-matroids/README.md) | Proof | 🟨 Partial · Lean 4 |

**Lean or Rocq key**　🟩 Full (entire statement) · 🟨 Partial (named components) · ⬜ None (no checked proof)

## Partial work

- For [balanced arrays](topics/balanced-arrays/README.md), every rank and dimension is covered through 24 rows. For arbitrary row counts, $d\ge(n+1)\log(2)/2$ suffices.
- For the [Eulerian square](topics/eulerian-matrix-square/README.md), every nonzero root in any fixed disk is eventually simple and negative. The all-row question remains open.
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
