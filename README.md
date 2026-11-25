# Open Problems in Mathematics

This repository publishes reviewed results on open problems across mathematics. The [result index](RESULTS.md) records their mathematical significance and formal proof status.

| Result | Rank | Scope | Lean or Rocq status |
|---|---:|---|---|
| [Prism-slice splitting fails](proofs/prism-splitting/README.md) | 1 | Disproof for every central split in the family with \(a\ge6\). | Lean 4 checks noninterlacing from the actual lattice-point counts through both dimension bounds, and the algebraic obstruction for the infinite family. |

## Splitting a bound can destroy interlacing for slices of prisms

For every integer \(a\ge6\), the central integral box slice of level \(a\) with bounds \((1^{2a-2},2)\) and the slice obtained by splitting the final bound into \((1,1)\) have Ehrhart numerators that fail to interlace. This disproves the splitting clause of Ferroni–McGinnis Conjecture 5.12. The real-rootedness of an individual prism-slice numerator remains an open question in general. [Original conjecture](https://doi.org/10.4153/S0008414X24000233)

[Mathematical paper](output/pdf/prism-splitting.pdf) · [TeX source](prism-splitting.tex) · [Ranked result index](RESULTS.md) · [Formal proof status](formalization/README.md) · [Review and prior work](REVIEW.md)

At \(a=6\), the degree-nine numerator has a real root below \(-850\), while the degree-ten numerator is strictly positive there. Both have simple negative roots. At every \(a\ge7\), the next leading coefficient of the lower-degree monic polynomial exceeds that of the higher-degree polynomial, contradicting the ordering forced by interlacing.

## Verify the result

~~~sh
python3 verify_counterexample.py
python3 verify_counterexample.py --emit
~~~

The verifier uses only the Python standard library. It reconstructs the coefficients from the bounded lattice counts, certifies the root intervals at \(a=6\), and checks the top-coefficient contradiction at \(a=7\). The [certificate](certificates/transport_split.json) contains the complete vectors, exact intervals and integer evaluations. The all-parameter argument is in the paper.

This branch publishes one reviewed result package. The broader research program is maintained privately.

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
