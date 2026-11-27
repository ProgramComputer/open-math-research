# Fourier numerator contraction for cutoffs eight and nine

At $k=8,9$, the original finite log numerator at an outer point and at the principal pole differs from the corresponding two contracted analytic log values by a sum of norms less than $65$. The radius band is $r\le R\le(1+1/k)r$, with $r=|s+i\pi|$ and $s\ge0$. The conclusion includes $s=0$. [Original numerator theorem](RepositoryEightNineNumerator.lean)

For $s\le8\sqrt{k}$, the normalized reciprocal sine scale is at most $13/5$. The radial slope remains $5/2$ because $e-e^{-1}+1/7<5/2$. The proof uses the original finite coefficients and the identified disk logarithm.

For $s>8\sqrt{k}$, use $d=78/1000$, $q=101/100$, split $2$, and decay $3/20$ in the positive-frequency estimate. The narrowest denominator is $8(3/20)-(d+q)=14/125>0$. The exponent estimates $e^{272/125}\le9$ and $e^{39/250}\le6/5$ give the strict total bound below $65$. [High-height adapter](EightNineHigh.lean) · [Rational constants](EightNineConstants.lean)

On the pinned Lean 4.33.1 toolchain, the checker builds the shared small-cutoff proof and replays the cutoff-eight and cutoff-nine modules.

```sh
python3 -Bu topics/long-cycle-excedances/lean/fourier-eight-nine/check.py /tmp/eight-nine-numerator
```

## Verification

The Linux build passed on Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The compiler inputs matched PR head `b261c98592d507fb1e07fef8229658bbd714e627` through GitHub checkout `aaf59bf5614adf2a7eecabb935896234856282b4`, the authenticated supplying archive, and the reproducibly applied mathlib-port patches. The report authenticated all 66 compiler input hashes and nine dependency revisions, with 50 kernel replays and 121 axiom reports using only `propext`, `Classical.choice`, and `Quot.sound`. Report artifact `15215247815` matched SHA-256 `4cbc26e93ab183e6dbb6b23b7d589d84b6fdb4d8f322c887a50e6a9cd8deae87`. The separate regression job for the original cutoffs 10 through 99 also passed with the generalized helper bounds. [Pinned build and replay](https://github.com/ProgramComputer/open-math-research/actions/runs/46032700543) · [Companion regression check](https://github.com/ProgramComputer/open-math-research/actions/runs/46032700439)

| Source | Compiler input SHA-256 |
| --- | --- |
| `EightNineConstants.lean` | `2e762f771bd0ece10a1e50db76d128f119bc6f25f856c79eb9940e329fb26391` |
| `EightNineHigh.lean` | `a0756820ac259bd15eff8bfa8277428c45f47708733466c4252cadfdcb39cc2b` |
| `RepositoryEightNineNumerator.lean` | `50e786ad750b2fa867ff0d83cfc72c7704ce889550207c2018a6e294a0699c8b` |
