# Literal cutoff numerator audit

Lean source head `07a70daa080153734818a1c131344d5027785550`. The retained hosted report has SHA-256 `79311b3a2b60262947f24a63ce19c12afae4443cd749ee6a9090b5efeaeb3a94`. [Successful hosted audit](https://github.com/ProgramComputer/open-math-research/actions/runs/45971276161)

Lean checked and kernel-replayed all 32 modules. All 58 required declarations reported only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. This run includes 18 new numerator declarations and the two existing probability declarations used by the numerator package. Every source hash in the report was compared with the exact Git object at the checked head. [Earlier paired-profile audit](occupied-verification.md)

```text
Frozen upstream source 46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554
Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)
mathlib 0df444a360eaa60ab8c11dca51a86af692955474
Reused verified common-pin archive sha256=000f5b74d9fe3aa351b19b0db90b4ab23b1e6329cbe6f6129b355f68b285cc05
Compile CycleNumeratorVariation input-sha256=63ab7cad34e4585a9d5dfa542c43f82a75d29d0b683a77b3d7ffe6f3d34e56b4
Compile CutoffCycleSeriesRecurrence input-sha256=a2d814eb4e7c9cc8c3dc71eea2118f21d2fc2bc4c7024b89ab94ac9b8c398c62
Compile RepositoryNumeratorVariation input-sha256=5be9e193db8b014780d5c91a09f1ce471f640ed9cc9f812687395f350a3a897a
kernel_replay_exit=0 CycleNumeratorVariation
kernel_replay_exit=0 CutoffCycleSeriesRecurrence
kernel_replay_exit=0 RepositoryNumeratorVariation
PASS: 58 paired-profile declarations audited
```

The literal theorem `OpenMathResearch.LongCycleExcedances.CycleProbability.coeff_cutoffCycleNumerator_eq_original` identifies the occupied-pole numerator coefficients with the original permutation probability differences for every natural degree and cutoff at least two. Its companion theorems give the first-block and factorial estimates. [Statement, module links, and checker](numerator-variation.md)
