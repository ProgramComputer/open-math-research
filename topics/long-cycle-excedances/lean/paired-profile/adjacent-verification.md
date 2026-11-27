# Verification of adjacent finite pole products and probability errors

**Passed on Lean 4.33.1.** At commit `ec89e7f8953e9beb45d232db80dcb81a8f4914d5`, the Linux job compiled 55 modules, replayed each with the Lean distribution’s `leanchecker`, and audited 104 named declarations. Each report used only a subset of `propext`, `Classical.choice` and `Quot.sound`. The compiler revision was `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, the mathlib revision was `0df444a360eaa60ab8c11dca51a86af692955474`, and the authenticated shared import archive had SHA-256 `000f5b74d9fe3aa351b19b0db90b4ab23b1e6329cbe6f6129b355f68b285cc05`. [Hosted build](https://github.com/ProgramComputer/open-math-research/actions/runs/45982147925) · [Source changes](https://github.com/ProgramComputer/open-math-research/pull/293/files)

The two original-enumerator applications are `original_window_determinant_lower` and `original_centered_probability_error`. The former takes an eventual lower bound on symmetric finite windows as its input. The latter checks the full piecewise probability error bound for the literal permutation probabilities at cutoffs at least 100. The convolution estimate `finite_principal_cost` uses a summable upper bound for its degree contributions. These theorems are steps in the all-size proof. [Statements and hypotheses](adjacent-windows.md) · [Original definitions and applications](RepositoryAdjacentWindows.lean)

Agent-assisted inspection matched each source digest against the Git object from the checked commit, checked every replay exit, and validated the 104 registered axiom reports and the pins in the downloaded log.

| Record | SHA-256 |
|---|---|
| [Hosted artifact](https://github.com/ProgramComputer/open-math-research/actions/runs/45982147925/artifacts/15190590092) | `d51ff70fe782a0076175c419a07f09018e7c9ab783b622dd51b272a3b0d18e3d` |
| Extracted `paired-profile.log` | `889d6758a745a7abb1a6ac68d901e65495d2049be72c780091132e64c9a9aa26` |
| `RepositoryAdjacentWindows.lean` | `cd2c57ab2dc8ff8e813debbaa4c19d70afddedc273e6bb0d48a912033f2fdfc6` |

From the repository root run

~~~sh
python3 -I topics/long-cycle-excedances/lean/paired-profile/check.py /tmp/adjacent-windows-verification
~~~
