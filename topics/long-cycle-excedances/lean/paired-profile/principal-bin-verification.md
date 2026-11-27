# Verification of the centered principal bin bound

Both production audits passed at source head `76d145afc7c0ba48ccb461b1a24affe22a1ee0b9`. They used Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`, and frozen upstream source `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554`. The import archive was authenticated by SHA-256 `000f5b74d9fe3aa351b19b0db90b4ab23b1e6329cbe6f6129b355f68b285cc05`. [Source changes](https://github.com/ProgramComputer/open-math-research/pull/294/files) · [Source and manifest pins](../pinned-quotient/check.py)

The literal theorem `OpenMathResearch.LongCycleExcedances.original_slab_principal_head_tail` bounds the doubled centered principal convolution error at the original permutation probabilities. It applies to each finite pole set, old size $n\ge10000$, cutoff $k=j+2$, $ell k\le n\le Xk$ for a selected slab endpoint $X$, and angle with $\sin\theta>0$ and $n\sin^2\theta\ge6/5$. Its inputs include the initial coefficient $q_0$ equal to the integer scale and the rounded product recurrence at each index $m<240$. The output is the weighted sum of the first 241 certified bin bounds plus $1/10000$. Evaluating those recurrence coefficients and combining the other determinant terms remain separate proof obligations. [Original-permutation theorem](RepositoryPrincipalSlab.lean) · [Statement and bin reduction](principal-bin-cost.md)

The paired-profile audit compiled and replayed 81 modules with the Lean distribution’s `leanchecker` and checked 124 named declaration axiom reports. The primitive audit staged and compiled 41 modules, replayed its 16 root modules, and checked 35 named declaration axiom reports. Inspection matched the recorded source digests against the exact Git objects, checked every replay exit, and confirmed that the two logs agreed on all 40 shared compiled inputs. The named declarations used only subsets of `Classical.choice`, `Quot.sound`, and `propext`. The literal slab theorem uses all three. [Paired-profile job](https://github.com/ProgramComputer/open-math-research/actions/runs/45986054495/job/140461843159) · [Primitive-envelope job](https://github.com/ProgramComputer/open-math-research/actions/runs/45986054423/job/140461888877)

The exact rational table and its independently generated row summary reproduced the hosted output. Comparing the Lean-evaluated linear table against the exact Python formula matched all 241 entries at each of the nine upper aspect endpoints. This covers the linear input table for the recurrence. [Rational comparison](../sine-comparison/verify-linear.py) · [Lean table comparison](../sine-comparison/compare-linear-table.py)

| Record | SHA-256 |
| --- | --- |
| [Paired-profile artifact](https://github.com/ProgramComputer/open-math-research/actions/runs/45986054495/artifacts/15193185525) | `a24876adc0dc3bb1b95f495c72aaee9ebfaccc9295a86c39cb66fcb1aaa5724f` |
| Extracted `paired-profile.log` | `76e32c4458590e2577d2520785da7e3dabf853070e983e7c85b3e6276e884362` |
| [Primitive-envelope artifact](https://github.com/ProgramComputer/open-math-research/actions/runs/45986054423/artifacts/15192210068) | `a32fa67ac54a64a6b6507f753f9e99162e80ce6b4b57b1a9b7d50552fe4ab46d` |
| Extracted `primitive-envelope.log` | `cc1cd9b5c5c5da323b730962eb080e157ca1c5332cf5b3e7ed792c87f034f622` |
| Extracted `linear-lean-output.txt` | `a0df998c4f2c700d795dccd8b6681a7f3c7e03ecdb48335627707001bf30b701` |
| Extracted `linear-output.txt` | `cb5668b288d45eb4bafc33d082a552d093bfd423c6a236a21ef0e3389496dd62` |
| `PrincipalBinHeadTail.lean` | `745df4b3c7ece5d9e3cee0d41a16d783df293982becfa6ca6407e72a11b52574` |
| `RepositoryPrincipalSlab.lean` | `c51b36bb8b08e85b8233f1e6a4e54e58a5087a144b78795286062041929dc3ab` |

Use the pinned toolchain and fresh scratch paths. [Paired-profile driver](check.py) · [Primitive-envelope driver](../sine-comparison/check-primitive-envelope.py)

~~~sh
python3 -I topics/long-cycle-excedances/lean/paired-profile/check.py /tmp/verify-principal-bin-cost
python3 -I topics/long-cycle-excedances/lean/sine-comparison/check-primitive-envelope.py /tmp/verify-primitive-envelope
python3 -I topics/long-cycle-excedances/lean/sine-comparison/verify-linear.py
~~~
