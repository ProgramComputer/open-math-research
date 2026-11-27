# Verification of the coarse moment bounds

For every natural lower aspect and bin and each integer upper aspect from 1 through 48, `coarse_bin_moments` bounds both real signed-pole moment majorants by their selected integer entries divided by the exact scale. The cap uses eight shapes. These moments contribute to the determinant budget. [Formal statement and proof](CoarseBinMoments.lean)

The production check compiled and replayed all 92 modules and checked the allowed axioms for 149 declarations, including all six new moment theorems. Each compiled input's SHA-256 matched its Git source at `05aebcaabfe4e526c4700c64c1c8f8444cb42a2a`. The only reported axioms were `propext`, `Classical.choice` and `Quot.sound`. The replay used Lean's bundled `leanchecker`. [Hosted run](https://github.com/ProgramComputer/open-math-research/actions/runs/45994932563) · [Report ZIP](https://github.com/ProgramComputer/open-math-research/actions/runs/45994932563/artifacts/15196577228)

The run used Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. The report ZIP SHA-256 is `aee00c5c811fc83192447390601fb10d7df9433ffc3a8394170b09c20d918841`. With the pinned Lean and Lake on PATH, run this command at the source revision.

```sh
python3 -Bu topics/long-cycle-excedances/lean/paired-profile/check.py /tmp/verify-coarse-moments
```
