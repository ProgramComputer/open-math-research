# Principal-cost certificate replay

The [paired-profile package](../paired-profile/principal-cost-certificate.md) was checked on the exact proof source commit `c3db479af676aac1dde0af650d8474149abf001a`. The [hosted build and artifact](https://github.com/ProgramComputer/open-math-research/actions/runs/45990964608) use Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and frozen upstream source `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554`. Replay is through the [paired-profile driver](../paired-profile/check.py).

The 90 compiled or evaluated Lean source hashes match the Git blobs. The run reports 86 successful Lean checker replays and 136 required declarations with axioms drawn from propext, Classical.choice and Quot.sound. It includes `original_slab_principal_le_computed_cap`, `fixedPrincipalCaps_ledger`, and `original_slab_principal_le_fixed_cap`.

The direct recurrence and the frozen product ledger have identical output SHA-256 `4423f9b4f31aea3b967a2199f78a12be5ca4f5282adb5e57023e43338b38ec62`. The independent Python checker agrees on every one of the 2169 product values and the fixed caps 72559, 12006, 643, 104, 101, 101, 101, 101 and 101, in millionths. The logical fixed-cap theorem has the ledger-equality premise, which this executable comparison checks. The computable cap in the original-row theorem has no ledger premise.

The console record `paired-profile.log` has SHA-256 `91faa0ce67100505d5f0e46767bd8acb1b7ac8415eba35426afbe9c6f7380bae`.
