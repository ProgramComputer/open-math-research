# Verification of the regular numerator error bound

The production audits passed at source head `19c543bb2b421b27169e0cd7368a1a12a5f7d4ea`. The Lean jobs used Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`, and frozen upstream source `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554`. They authenticated the import archive by SHA-256 `000f5b74d9fe3aa351b19b0db90b4ab23b1e6329cbe6f6129b355f68b285cc05`. [Source changes](https://github.com/ProgramComputer/open-math-research/pull/296/files) · [Frozen source and manifest pins](../lean/pinned-quotient/check.py)

The theorem `OpenMathResearch.LongCycleExcedances.original_regular_numerator_head` bounds the finite absolute regular-numerator cost for the original cutoff permutation probabilities. Its hypotheses are an old size $n\ge10000$, a positive lower aspect integer $\ell$ and a selected upper slab endpoint $X$ with $\ell k\le n\le Xk$, and an angle with $\sin\theta>0$ and $n\sin^2\theta\ge6/5$. The sum includes every pole in the chosen finite set and the successor terms at degrees $s=n+1-t>k$. The theorem takes the initial rounded product coefficient and the 240 integer recurrence inequalities as inputs. The isolated term at degree $s=k$ and the determinant assembly require separate arguments. [Original theorem](../lean/paired-profile/RepositoryRegularCost.lean) · [Statement and strict block argument](regular-numerator.md)

The paired-profile audit compiled and replayed 89 modules with the Lean distribution’s `leanchecker` and audited 143 named declaration axiom reports. The primitive audit staged and compiled 41 inputs, replayed its 16 root modules, and audited 35 named declarations. Inspection matched both reports to the Git source objects, checked the replay exits, and confirmed agreement on 40 shared compiled inputs. Each axiom report used only a subset of `Classical.choice`, `Quot.sound` and `propext`. The original theorem and `regular_numerator_strict_bin` use all three. [Paired-profile job](https://github.com/ProgramComputer/open-math-research/actions/runs/45988295231/job/140469391930) · [Primitive-envelope job](https://github.com/ProgramComputer/open-math-research/actions/runs/45988295055/job/140469391219)

An independent rerun of the exact Python checker reproduced the checked-in nine ceilings in millionths, `6068, 2565, 198, 3, 1, 1, 1, 1, 1`. Recomputing the bounds with the separately evaluated product-coefficient ladder gave the same ceilings. The primitive job and independent comparison also matched all 241 entries at each of the nine upper endpoints of the linear input table. The Lean inequality still has the rounded product recurrence as a hypothesis. [Hosted rational check](https://github.com/ProgramComputer/open-math-research/actions/runs/45988295130/job/140469390891) · [Exact Python checker](check-regular.py) · [Recorded ceilings](regular-output.txt)

| Record | SHA-256 |
| --- | --- |
| [Paired-profile artifact](https://github.com/ProgramComputer/open-math-research/actions/runs/45988295231/artifacts/15193717243) | `9b4e66f5694d2f10536f3ffd8b191ff21503aed1aeb9f65bc9b49d98d90fa38a` |
| Extracted `paired-profile.log` | `97d0a9322d46c65e0090e294f87eef946c5ec76baf5827ceada51281eb00c7ed` |
| [Primitive-envelope artifact](https://github.com/ProgramComputer/open-math-research/actions/runs/45988295055/artifacts/15192767154) | `88264c6ef41d07754b5c016e15865ebb5319bfef46ee1c2a1fdad04ca348820a` |
| Extracted `primitive-envelope.log` | `72a75c5cba29d3b99b94bf44dd3f34f7b2d9f82e09cfbf53a4ae68c8262f42f2` |
| `regular-output.txt` | `d931f677f7a936c02568a841587209d280f03afc85eded1f7af87c5909a61f7b` |
| `RegularNumeratorBin.lean` | `853f14d0452867b7add7730e127c1b4153cd5409e5ea43edce5a8d7a02015ce8` |
| `RegularValueCost.lean` | `5c31ed4e0e118baeec7ea1e1fef9ae77ae9d5d65015a437358e7949ef94d1cee` |
| `RepositoryRegularCost.lean` | `44c421b2c73961056cdf5adbcd083b09cfc6527e5cfbadac418d7c8cb9dcc8c2` |

Use the pinned toolchain and a fresh scratch path for each Lean build. [Paired-profile driver](../lean/paired-profile/check.py) · [Primitive-envelope driver](../lean/sine-comparison/check-primitive-envelope.py)

~~~sh
python3 -I topics/long-cycle-excedances/lean/paired-profile/check.py /tmp/verify-regular-numerator
python3 -I topics/long-cycle-excedances/lean/sine-comparison/check-primitive-envelope.py /tmp/verify-regular-primitive
python3 -I -B topics/long-cycle-excedances/sine-comparison/check-regular.py
~~~
