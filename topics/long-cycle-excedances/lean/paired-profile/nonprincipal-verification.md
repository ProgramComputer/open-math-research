# Verification of the nonprincipal value error

**Passed on Lean 4.33.1.** The production job at `b8671ed816b1a0ffa77c1f312478a05700bd8355` compiled and replayed all 86 input modules with the distribution's `leanchecker`. Agent-assisted verification matched all 86 SHA-256 input digests to the Git objects at that commit and all 86 replay exits to the build manifest. All 136 registered declaration reports contained only allowed standard axioms. The formal theorem `original_nonprincipal_value_head` depends on `propext`, `Classical.choice` and `Quot.sound`. [Build](https://github.com/ProgramComputer/open-math-research/actions/runs/45986385028) · [Theorem](RepositoryNonprincipalCost.lean)

The theorem bounds the nonprincipal value error of the original permutation enumerator on every finite pole set by the rounded product head on each of the nine intervals. It assumes the initial product coefficient and the finite integer recurrence inequalities. The fixed numerical ceilings were checked by exact rational arithmetic. Computing them again using the separately evaluated Lean product coefficients gave the same nine values. Combining the four determinant errors and proving the complete all-size root lists are further obligations. [Proof and ceilings](../../sine-comparison/nonprincipal-value.md) · [Rational workflow](https://github.com/ProgramComputer/open-math-research/actions/runs/45986385022) · [Primitive-envelope workflow](https://github.com/ProgramComputer/open-math-research/actions/runs/45986385007)

| Item | Revision or SHA-256 |
|---|---|
| Lean 4.33.1 | `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` |
| mathlib | `0df444a360eaa60ab8c11dca51a86af692955474` |
| Shared imported objects | `000f5b74d9fe3aa351b19b0db90b4ab23b1e6329cbe6f6129b355f68b285cc05` |
| [Hosted ZIP](https://github.com/ProgramComputer/open-math-research/actions/runs/45986385028/artifacts/15193660192) | `b555332fb6489831f8eb6652ec2d2b792778af5507ce60e9670d581a45f5aa7f` |
| Extracted verification log | `d48d1f246b903ae7c9fd47629dca028780423ed385955b0b0ab166bb7c739e7c` |
| Original-enumerator source | `fc7215367ca02a37821f3efdeb93207861c6376d7d308ccc960b81e30a5f0f02` |

With the pinned Lean toolchain on the path, run from the repository root

~~~sh
python3 -I -B topics/long-cycle-excedances/lean/paired-profile/check.py /tmp/nonprincipal-proof
python3 -I -B topics/long-cycle-excedances/sine-comparison/check-nonprincipal.py
~~~

The build driver also accepts the verified shared import archive as an optional second argument. The rational calculation requires Python's standard library. [Production workflow](../../../../.github/workflows/long-cycle-paired-profile.yml)
