# Verification record

The production source at `152852afa8beb6db16b5b7e45c4eae03a66b2000` passed on Linux with Lean `4.33.1` at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. The common-pin driver authenticated Bowen Zuo's frozen cutoff-six source at `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554` for the supplied Eulerian and cycle-profile identities. Run `python3 -I -B check.py /path/to/new/project` from this directory. [Driver](check.py) · [Common supplying pin](../common-pin/README.md) · [Passing hosted run](https://github.com/ProgramComputer/open-math-research/actions/runs/46030869004)

The report archive has SHA-256 `94e272a0be1084e6bf3bc37421c57af65d3119ea48fb6183aa9124fb68564f52`. All 52 repository compiler readouts match the exact tracked inputs or their reproducible common-pin staged hashes. The 11 supplying module readouts match the previously authenticated frozen source record. The eleven new modules compiled and replayed with bundled LeanChecker. All 20 named declarations report only `propext`, `Classical.choice` and `Quot.sound`. The unconditional endpoints are `RepositoryQuotientAudit.original_small_cutoff_fifty_contraction` and `RepositoryQuotientAudit.original_small_cutoff_ten_contraction`. [Exact original statements](RepositorySmallCutoffNumerator.lean) · [Independent scope and arithmetic review](independent-review.md)

| Source | SHA-256 |
| --- | --- |
| [SmallCutoffPoisson](SmallCutoffPoisson.lean) | `7aa17aa3e69776a0e2fcd11657579f3f5462dcdc7fd85a8bcb2d354a83c0ed46` |
| [SmallCutoffFrequency](SmallCutoffFrequency.lean) | `83eafc04cb5327e15e689ded725eb2b80dc8d89604e9126e3c26bec560f94d66` |
| [HighBandNumerator](HighBandNumerator.lean) | `036499fdd5e3284cd27359932756f92bf2ef3c6042b146a540d041afa09eb3ba` |
| [HighBandConstants](HighBandConstants.lean) | `4c77f74affbda41112395c67936e04c4f3320f2b4c01662cb3797ee7981dbe84` |
| [SmallCutoffHighPoints](SmallCutoffHighPoints.lean) | `79b0c730546d64c951804061a0704e2992ae6fefc63c7e44d9715da323d34f4a` |
| [SmallCutoffHighBands](SmallCutoffHighBands.lean) | `b9c2176b68cfcffbb3ce4b99d539bfff2a76610cee602e34a390868a79208fb5` |
| [LowBandRadial](LowBandRadial.lean) | `cae38c27314742455f73a676be49b508f96e0d3d08fd7d0be83001bc994da625` |
| [LowBandContraction](LowBandContraction.lean) | `ebcbb47b17064dbdb9160c03a28656228a5d12671622abd8a7aaeecb09709807` |
| [LowBandLiteral](LowBandLiteral.lean) | `f7ff61ba07305e786b0db915665265bf62ee3af6ea7d8e6294a29740104d95a2` |
| [SmallCutoffLowPoints](SmallCutoffLowPoints.lean) | `c16f85ee1c17133681c3db3cca326f3a4efed9c4b3c1a3aa9245a4db86f32d62` |
| [RepositorySmallCutoffNumerator](RepositorySmallCutoffNumerator.lean) | `d824f4ca560e30771418a4f51bbe572cef524cf56a3162ac391b73ff296227e0` |

The initial run stopped before compilation because its workflow path omitted the directory's `fourier-` prefix. The next run replayed the low-height arm and the parameterized Poisson prefix, then diagnosed two common-pin API changes in the high-height tail helper. The passing run resolved those ports and completed with advisory tactic-linter warnings. The checked statements retain the original cutoff coefficients and analytic logarithm in both bands.
