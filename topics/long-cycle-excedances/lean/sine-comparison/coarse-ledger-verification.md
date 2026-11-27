# Coarse product ledger replay

The [nine-slab coarse product certificate](../paired-profile/coarse-recurrence-certificate.md) compiled at exact proof source commit `a6d2454b96dc7024ece9a03929d62eec14c20e5b`. The [paired-profile run](https://github.com/ProgramComputer/open-math-research/actions/runs/45994848754) uses Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and frozen upstream source `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554`.

All 125 compiled or evaluated source hashes match the corresponding Git blobs. The run reports 121 successful Lean checker replays and 181 required declarations with axioms drawn from propext, Classical.choice and Quot.sound. The added results include the signed-star caps, all nine recurrence shards, `coarseOriginalLedger_recurrence`, and `roundedQ_le_coarseOriginalLedger`. The latter two close the finite recurrence and dominance for the original analytic table.

The independent Python checker at SHA-256 `8cf0eeee96e7eed7d6e663910116147597f9f6a95fe08d6f6c1dfa6c021a1519` reproduced both coefficient arrays in all nine slabs. The `paired-profile.log` console record has SHA-256 `bbee71187cc8657d8171cc00cd6ed3920d35ff956bb7c881d353ea56769b1b23`. The [primitive-envelope run](https://github.com/ProgramComputer/open-math-research/actions/runs/45994848770) passed on the same proof source.

This certificate bounds the product-coefficient recurrence. The four determinant costs and sign proof use additional declarations.

The [combined replay](https://github.com/ProgramComputer/open-math-research/actions/runs/45998741835) passed on `0318cd80573e255b4fdd8a087680cc90674e42c4`, including the cutoff-jump and coarse-moment declarations. All 137 compiled or evaluated Lean inputs match the integrated Git sources. The report contains 133 successful kernel replays and 204 audited declarations, and the independent coarse ledger regeneration passed again. Its console SHA-256 is `41ef969f97c12f688c6dac93ce20b117d0894eb83666a0d1a5d38a8472ad5673`.
