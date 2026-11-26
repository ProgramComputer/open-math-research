# Verification of marked-row pairings and orientations

**🟨 Partial · Lean 4.** The two modules connect actual labeled binary arrays with orientations of a fixed column pairing, count how many pairings refine an array pair, and check the local pairing and overlap calculations. The orientation inequality across two different degree constraints, the marked-row pairing average over exchangeable residual rows, and the geometric sign argument still have written proofs. The million-row polynomial has no end-to-end formal proof. [Combinatorial statements](../README.md) · [Finite review](../finite-review.md)

## Weighted pairings and overlaps

[Lean declarations](MarkedPairing.lean) · [Axiom report](axioms.txt)

| Checked declaration | Mathematical content |
| --- | --- |
| `weight_nonneg` | Every allowed pairing receives a nonnegative rational weight. |
| `sum_hit`, `column_sum` | A permutation models a labeled bijection. Summing over all partners of the auxiliary slot gives the two column multiplicities, including a specified blue-only mark. |
| `all_columns` | Summing the product of pairing weights over independently chosen column bijections gives the product of the column sums. |
| `cancel_common_marks` | The weighted source versus target comparison implies the claimed factor after cancellation. The comparison itself is a hypothesis here. |
| `sharp_binomial_factor` | The two explicit binomial counts attain the proposed factor at every positive integer parameter and every exponent. |
| `overlap_profile_card` | Among subsets of actual row labels, the number with specified overlap and specified number outside a fixed blue set equals the product of two binomial coefficients. |
| `removedWeight_mul`, `removed_probability`, `retained_probability` | Vandermonde’s sum gives the exact removed and retained probabilities for arbitrary margins $`a<b\le n`$. The Lean parameters are $`b=a+u+1`$ and $`n=b+c`$. |

## From labeled arrays to orientations

A column pairing is an involution of the row labels in each column. At its fixed points both arrays have the specified common bit. Each two-cycle contributes one directed edge with labeled endpoints. Its tail is occupied in the red array and its head in the blue array. Additional row labels accommodate auxiliary cells. [Lean declarations](ArrayOrientation.lean) · [Axiom report](orientation-axioms.txt)

| Checked declarations | Mathematical content |
| --- | --- |
| `arrayEquiv`, `constrained_count` | A bijection recovers both labeled matrices from the edge directions. Arbitrary predicates on the resulting pair can be imposed before counting. |
| `outgoingEquiv`, `red_row_size`, `blue_row_size`, `row_constrained_count` | Exclusive cells correspond bijectively to incident edges of the appropriate direction. All red and blue row-size constraints transfer to degree constraints, including distinct bounds on the two colors. |
| `red_column_size`, `blue_column_size` | Both augmented column sums equal the number of fixed occupied slots plus the number of paired edges in that column. |
| `splitOutgoingEquiv` | Any labeling of individual incidences can split a row into vertices. The outgoing edges at each such vertex correspond to the red-exclusive slots there. |
| `ofMatchings_compatible`, `refinementsEquiv`, `refinement_count_of_quotas` | Given two actual matrices with equal augmented column totals, normalized compatible pairings correspond to the columnwise bijections of exclusive slots. Their number is the product of one factorial for each column, also when the exclusive sets are empty. |

The first eight declarations of the orientation module were independently checked against the written argument and rebuilt by a separate agent using the research pin. Its source digest for that check was `e9b982bde52703965e93dc552e52ccbce992ef41bbf411f363332022fa049a96`. The last four declarations extend that initial module. The orchestrator rebuilt the entire checked-in source and audited all twelve declarations.

## Research build

On 26 November 2026 both sources compiled with Lean 4.19.0 at `6caaee842e9495688c1567e78c0e68dbb96942aa` and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The 22 axiom reports contain subsets of `propext`, `Classical.choice` and `Quot.sound`. [Shared toolchain](../../../../shared/lean/lean-toolchain) · [Dependency manifest](../../../../shared/lean/lake-manifest.json)

With the locked dependencies available, run from the repository root.

~~~sh
cd shared/lean
lake env lean ../../topics/balanced-arrays/marked-row-likelihood/lean/MarkedPairing.lean
lake env lean ../../topics/balanced-arrays/marked-row-likelihood/lean/ArrayOrientation.lean
~~~

Each module prints its own axiom audit. The local run invoked the same compiler with `LEAN_PATH` pointing to the compiled packages in the locked manifest. In a fresh checkout, `lake exe cache get` fetches the pinned mathlib build artifacts.

## Stable build

On 26 November 2026 the hosted audit built both modules from repository commit `5cc486a58171319924acf9cccb2eb77ca746f405` with Lean 4.36.0 release commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9` and mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The 22 declaration reports list only `Classical.choice`, `propext`, and `Quot.sound`. [GitHub Actions run](https://github.com/ProgramComputer/open-math-research/actions/runs/45892169890) · [Original artifact](https://github.com/ProgramComputer/open-math-research/actions/runs/45892169890/artifacts/15151389033) · [Archived axiom reports](stable/record/axioms.json) · [Lean version](stable/record/lean-version.txt) · [Mathlib revision](stable/record/mathlib-revision.txt)

The [source record](stable/record/sources.json) gives SHA-256 hashes for the original and staged files. Restaging the inputs from the audited commit reproduced both sets of hashes. The [orientation port](stable/ArrayOrientation.patch) unfolds the decoded pair explicitly in two branches of the compatibility proof. The [pairing port](stable/MarkedPairing.patch) uses the current positive-factor cancellation lemma in one proof. Both ports change proofs in the staged copies and preserve the declaration statements. Lean coverage remains partial as described above.

To reproduce the hosted audit, use Bash from the root of a clean checkout with Elan and the pinned stable toolchain available.

~~~bash
set -euo pipefail
git checkout --detach 5cc486a58171319924acf9cccb2eb77ca746f405
audit_script=topics/balanced-arrays/marked-row-likelihood/lean/stable/audit.py
python3 "$audit_script" stage .marked-row-stable
(
  cd .marked-row-stable
  lean --version | tee lean-version.txt
  grep -E '^Lean \(version 4\.36\.0,' lean-version.txt
  lake --version
  mapfile -t imports < cache-imports.txt
  lake exe cache get "${imports[@]}"
  test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
  lake build MarkedPairing ArrayOrientation
)
python3 "$audit_script" audit .marked-row-stable
~~~
