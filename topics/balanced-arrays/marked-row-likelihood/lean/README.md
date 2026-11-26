# Verification of the marked-row pairing calculations

**🟨 Partial · Lean 4.** Ten theorems check the local pairing counts, their product across columns, cancellation of the common mark factor, the sharp binomial ratio, and the overlap computation used for the exact odds. The orientation comparison on two colored arrays, the use of row exchangeability, the likelihood theorems and the root conclusions have written proofs. The million-row polynomial has no end-to-end formal proof. [Lean source](MarkedPairing.lean) · [Exact axiom report](axioms.txt) · [Original combinatorial statements](../README.md)

| Checked declaration | Mathematical content |
| --- | --- |
| `weight_nonneg` | Every allowed pairing receives a nonnegative rational weight. |
| `sum_hit`, `column_sum` | A permutation models a labeled bijection. Summing over all partners of the auxiliary slot gives the two column multiplicities, including a specified blue-only mark. |
| `all_columns` | Summing the product of pairing weights over independently chosen column bijections gives the product of the column sums. |
| `cancel_common_marks` | The weighted source versus target comparison implies the claimed factor after cancellation. The comparison itself is a hypothesis here. |
| `sharp_binomial_factor` | The two explicit binomial counts attain the proposed factor at every positive integer parameter and every exponent. |
| `overlap_profile_card` | Among subsets of actual row labels, the number with specified overlap and specified number outside a fixed blue set equals the product of two binomial coefficients. |
| `removedWeight_mul`, `removed_probability`, `retained_probability` | Vandermonde’s sum gives the exact removed and retained probabilities for arbitrary margins $`a<b\le n`$. The Lean parameters are $`b=a+u+1`$ and $`n=b+c`$. |

The source was checked on 26 November 2026 with the shared research pin, Lean 4.19.0 at commit `6caaee842e9495688c1567e78c0e68dbb96942aa` and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The compiler exited successfully and the ten axiom reports contain only `propext`, `Classical.choice` and `Quot.sound` or a subset. No declaration uses a proof placeholder or a project-specific axiom. Independent kernel replay of the complete mathematical theorem remains outside this partial check. [Shared toolchain](../../../../shared/lean/lean-toolchain) · [Dependency manifest](../../../../shared/lean/lake-manifest.json)

With the locked dependencies and their compiled artifacts available, run from the repository root:

~~~sh
cd shared/lean
lake env lean ../../topics/balanced-arrays/marked-row-likelihood/lean/MarkedPairing.lean
~~~

The session used the compiler from that exact toolchain with `LEAN_PATH` populated from the locked packages’ compiled library directories. The checked source prints the axiom report at the end of each clean invocation. To fetch a missing mathlib build cache in a fresh checkout, use `lake exe cache get` from the same shared Lean directory.
