# Common-pin verification of the small-height cutoff contraction

The hosted [common-pin check](https://github.com/ProgramComputer/open-math-research/actions/runs/46016238078) compiled the literal cutoff bridge and all modules used by [the small-height bound](README.md) at [commit b8fc5b6](https://github.com/ProgramComputer/open-math-research/tree/b8fc5b6c1a7573e870f7fdd828f64131bb2c2020). It used Lean 4.33.1 at compiler commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6 and mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. The checker rebuilt the supplying original cutoff bridge using the authenticated cutoff-six import and the saved common-pin dependency objects.

All 15 named numerator declarations report only propext, Classical.choice, and Quot.sound. The bundled LeanChecker replayed all 7 theorem modules with exit code zero. The exact shared definition file compiled and its definitions were imported by the replayed proofs. I compared the three relocated definition bodies and each ported theorem statement with the source of the [4.19 verification](../fourier-circle/numerator-small-height-verification.md). The 4.19 workflow also rebuilt the extracted definitions and all their existing clients. [Legacy-pin check](https://github.com/ProgramComputer/open-math-research/actions/runs/46014502245).

The original polynomial in [NumeratorCutoffAdapter.lean](NumeratorCutoffAdapter.lean) uses the cutoff-log coefficients at the actual parameter given by the negative exponential of the height. [NumeratorSmallHeightPoints.lean](NumeratorSmallHeightPoints.lean) gives the same bound at the literal outer and principal points and assumes an analytic HasSum identification on the open unit disk. The uniform bound is 2997/100 for cutoff at least 100 and height between zero and four times the square root of the cutoff, inclusive.

[Report artifact 15206348102](https://github.com/ProgramComputer/open-math-research/actions/runs/46016238078/artifacts/15206348102) has ZIP SHA-256 a97aa178073f0c7ab2c6a6f1dcbfc4e24e21eebc365571d107d70478cbbdc29d and log SHA-256 33ddeb95cc4fc401bf77695cdd9b121380c786bd148c16b98e5d56fc57beefd5.

| Module | Compiled input SHA-256 |
| --- | --- |
| NumeratorPoleVolume | 7843c515c200772a1131ae3a8838d114d4a9de6effa62125d77a6ef17877c86d |
| NumeratorLogDefinitions | 5b6c8d318b2d5f734c72a8b07087e929cc9e3edbac0109d82d9fdab7f8e765d1 |
| NumeratorOddPoleMoment | a48dd55d753a455fe4ffd445bc1f3169c6d12431b6bea9ed159c48cae96ca319 |
| NumeratorRadialScalars | 9e1cf9dd929ac2166dac92e493c2529955f5aca24c1afed8f27e9d229714a48a |
| NumeratorTaylorContraction | a32c15a76cb3df0de7db6e9244e4500ea94c6e0650c4010ad7e9a8c4acab5df8 |
| NumeratorLogSeries | 05ff1f3b178e8974cd69550aab2031e5ea2604c12399343796a004a1c51d048d |
| NumeratorCutoffAdapter | 23a513e46d9a6ea5f82bd3e69cb0096bfa0ed23e8daf711f80282bd2aa8480a7 |
| NumeratorSmallHeightPoints | 581ee05c4308694d6aa2a8b942e9f8a06e5d3c7be9add22d3b4ac5c548142041 |

The checked original-log-only prerequisite followed the same compilation and replay steps after integrating the new Fourier continuation and [full-disk logarithm identity](../fourier-stable/analytic-log-series.md). All numerator and original cutoff proof inputs match the hosted run.
