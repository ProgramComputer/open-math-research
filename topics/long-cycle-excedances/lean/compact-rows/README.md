# Rounding the insertion recurrence for strict excedances

For a cutoff $k\ge2$, let $c_{n,j}$ count the permitted permutations of $n$ labels with $j+1$ strict excedances. The recurrence in this directory rounds each updated coefficient down to its first $b$ significant binary digits. Write $L_{n,j}$ for the resulting integer. The Eulerian coefficients multiplying the lagged row remain exact.

Lean checks the coefficient enclosure

$$
0\le L_{n,j}\le c_{n,j},\qquad (1-n2^{1-b})c_{n,j}\le L_{n,j}.
$$

In particular, at $b=48$, for $n\le1001$, $y\ge0$ and any prefix width $w$,

$$
\left|\sum_{j<w}(c_{n,j}-L_{n,j})(-y)^j\right|
\le 2^{-36}\sum_{j<w} L_{n,j}y^j.
$$

The seed at $n=k$ is the ordinary Eulerian row on $k-1$ labels. The proof checks that the natural-number recurrence also agrees above the support, where an integer subtraction would change sign. The packing lemmas recover each rounded coefficient from its significand and shift and give a 64-bit storage bound in the archive range.

[Literal permutation theorem](RepositoryCompactRows.lean) · [Combinatorial coefficient recurrence](OriginalRoundedRows.lean) · [Rounding analysis](TruncatedRows.lean) · [Packing model](CompactRowModel.lean)

## Verification

All four modules passed the pinned Lean 4.33.1 build and module replay. The 20 printed axiom reports contained only standard axioms. The first port attempt stopped on a local identifier newly reserved by Lean. Renaming it allowed the same mathematical argument to compile. The two complete C++ sign runs independently reproduced all 2,164,796 strict signs. A kernel check of the complete finite archive and of the analytic joins remains open. [Hosted source and results](hosted-audit.txt) · [Independent agent review](independent-review.md) · [Existing exact integer sign verification](../../intermediate/integer-signs/README.md)

To rebuild from the repository root on Lean 4.33.1, with mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`, use a fresh destination directory.

```sh
python3 topics/long-cycle-excedances/lean/compact-rows/check.py /tmp/compact-row-build
```

The script authenticates the supplying cutoff-six sources, checks the dependencies, audits theorem axioms and runs Lean's `leanchecker` on each new module. [Pinned dependency record](../common-pin/README.md)
