# Verification of the quantitative principal contribution

**Passed on Lean 4.33.1.** The build at `487393ad18fc22733c91e3864971b660635ff613` checked `original_scaled_principal_all` and `original_scaled_principal_low`. These theorems give uniform lower bounds for the scaled real part of the original principal pole product in the two stated size ranges. The adjacent-row determinant also uses four error estimates whose formal verification is in progress. [Exact statements](../lean/paired-profile/PrincipalScaledBudget.lean) · [Mathematical argument](reflected-carrier.md) · [Hosted build](https://github.com/ProgramComputer/open-math-research/actions/runs/45979598948)

The compiler revision was `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, mathlib was `0df444a360eaa60ab8c11dca51a86af692955474`, and the shared import archive had SHA-256 `000f5b74d9fe3aa351b19b0db90b4ab23b1e6329cbe6f6129b355f68b285cc05`. Agent-assisted inspection matched all 45 source digests against Git, confirmed all 45 replay exits from the Lean distribution’s `leanchecker`, and checked 84 named axiom reports. Every registered theorem uses at most `propext`, `Classical.choice` and `Quot.sound`. The separate rational checker reproduced all nine determinant margins using the previously reviewed error estimates. [Exact checker](check-reflected.py) · [All nine margins](reflected-output.txt)

| Record | SHA-256 |
|---|---|
| [Hosted proof log archive](https://github.com/ProgramComputer/open-math-research/actions/runs/45979598948/artifacts/15188454306) | `3a696ae88ad81b596f6b7fadbf569c7a7d1c0e00cb950fd40df5731d9a42bb5b` |
| Extracted `paired-profile.log` | `5862d9bb716fc4a4742a443148914c2f0e68fbf07f38f94d8cd697f0a0cd7cde` |
| `PrincipalScaledBudget.lean` | `11e554275983eadfd5aad3a94211fdcd837de90e3e768367e1a97074ceeb0d52` |

From the repository root, run

~~~sh
python3 -I topics/long-cycle-excedances/lean/paired-profile/check.py /tmp/reflected-principal-verification
python3 -I topics/long-cycle-excedances/sine-comparison/check-reflected.py
~~~

The first production attempt exposed two tactic porting errors in the conjugate-term calculation. The archived build used the corrected derivation and passed.
