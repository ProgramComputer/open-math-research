# All-aspect exterior verification

On 27 November 2026, both hosted Lean audits passed for PR head `b49eae93dacda54650d239d7468fd37c4dc4c2a3`. The compiled sources and the module and axiom reports were compared against the checkout of that head. The mathematical review independently checked the grid reduction, the finite arithmetic, and the statement at the original enumerator. [PR #287](https://github.com/ProgramComputer/open-math-research/pull/287) · [Independent review](independent-review.md)

The theorem `RepositoryQuotientAudit.original_all_aspect_exterior` gives an increasing list of positive moduli of distinct negative zeros of the literal enumerator at size $n$ before the first integer seam. It gives the strict successor sign $(-1)^{i+2}$ at each modulus, with $i$ starting at zero. Its hypotheses are $n\ge10000$ and $2\le k\le n$. With the separately checked near-lag bound, the companion theorem locates a root with the successor sign in each prescribed coefficient window. Establishing exact ordinal ranks, simplicity, and all remaining roots requires further arguments. [Top-level exterior theorem](AllAspectExterior.lean) · [Companion window theorem](RepositoryAllAspectExterior.lean)

## Toolchain and reports

- Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. The workflows recovered the frozen source at `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554` and reused the digest-checked 65-module import archive with SHA-256 `000f5b74d9fe3aa351b19b0db90b4ab23b1e6329cbe6f6129b355f68b285cc05`. [Source and manifest pins](../pinned-quotient/check.py) · [Common audit driver](../common-pin/check.py)
- The standalone audit matched 151 compile input hashes and recorded 134 successful Lean kernel replays and 290 named declaration axiom reports. The log SHA-256 is `59fa014a43e4171a5b7594968b418c2d0ea588805e0e041cd0bb377b571dfb7d`. [Standalone job](https://github.com/ProgramComputer/open-math-research/actions/runs/45982691921/job/140450354764) · [Archived log](https://github.com/ProgramComputer/open-math-research/actions/runs/45982691921/artifacts/15191341192)
- The composed audit matched 173 compile input hashes and recorded 156 successful Lean kernel replays and 350 distinct named declaration axiom reports. The log SHA-256 is `a7d67812855a8e907c5096885b59353733dd5bfd6c843751fdca6fa0e37b95fb`. [Composed job](https://github.com/ProgramComputer/open-math-research/actions/runs/45982691686/job/140450353477) · [Archived log](https://github.com/ProgramComputer/open-math-research/actions/runs/45982691686/artifacts/15190593922)
- The transitive axiom reports for the top-level theorem and its window companion list `Classical.choice`, `Quot.sound`, and `propext`. The audits checked the named declarations against this same allowed set. Replay used the pinned Lean toolchain's `leanchecker`.

The following changed or new Lean inputs matched the hosted compiler input digests. Each module compiled and its `leanchecker` replay succeeded.

| Module | SHA-256 |
| --- | --- |
| `RepositoryColorAlpha` | `390a50f7a10249ff789b85dc77f935839bad95e769751294b13859fbab3a6887` |
| `RepositoryOldFrontTails` | `1947d7ef4fb371d4786397c0dabee02d142ac1f58759c78b5dd61929a042cbd3` |
| `ResidualLagGrid` | `b6875bb4d33d5f2507410b462f563ccfc99cf39a278711e3b8c96d9ae2938f5f` |
| `SharpLagBudget` | `dac6cb1d657fee11cdc21f2d5e55d50a998a874b266c2985d2a41fc23d49e365` |
| `OriginalResidualLag` | `8a9ab4465964110d0460e5d72d5cc2ffa71406416bd6bdef5674e191d03e76fb` |
| `TwoGridLag` | `197fe200a1e3f52ae1b76b6c34a2d9ae09c8b0d17b513a862587ec53b25f785e` |
| `ZeroResidualLag` | `da9427f4ef3622f071e86e0e6bd6d1ef5ce369280b7bd869a9602e1ae0df5abd` |
| `RepositorySharpNearLag` | `7ed2a97b87870ee849a060e3eaf6836791b3b1959d82ec3d302b342602754de3` |
| `ExteriorIntegerSeam` | `3a00519f28682bcfab8ae448cedcf217660a8b86f2d4b17633a3bf4d6b13ac9a` |
| `RepositoryAllAspectExterior` | `102ba5605fd0115664981cb7d6f1c9dfafac87f9dca8eb0409a3896223c61de1` |
| `AllAspectExterior` | `a995f016c94ea99e142b9daf2c76f2a558db544ab3c59616ca58eda1f11fdaeb` |

## Reproduction

Use the pinned Lean toolchain and two fresh build directory names. The drivers fetch and check the frozen source and manifest in either case. To reuse the audited import archive, pass its path as a second argument to either driver. [Standalone workflow](../../../../.github/workflows/long-cycle-common-pin.yml) · [Composed workflow](../../../../.github/workflows/long-cycle-front-envelope-sums.yml)

~~~sh
python3 -Bu topics/long-cycle-excedances/lean/common-pin/check.py /tmp/exterior-common-audit
python3 -Bu topics/long-cycle-excedances/lean/front-envelope-sums/check.py /tmp/exterior-composed-audit
~~~
