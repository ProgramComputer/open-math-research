# Mixed root witnesses in Lean

The theorem `OpenMathResearch.LongCycleExcedances.interlace_of_mixed_root_witnesses` checks the separating-point step in the long-cycle excedance argument. It applies to real polynomials $P$ and $Q$ of degrees $m$ and $m+1$, with $P\ne0$, positive $Q(0)$ and positive leading coefficient of $Q$. In increasing positive modulus order, each of the $m$ disjoint closed windows $[l_i,u_i]$ is either a known old root or has opposite signs of $P(-x)$ at its endpoints. At both endpoints of window $i$ the sign of $Q(-x)$ is $(-1)^{i+1}$, where $i$ starts at zero. [Lean theorem](LongCycleMixedRootWitnesses.lean#L18) · [Intermediate certificate and argument](../intermediate/README.md#independent-separating-point-check)

The theorem gives complete ordered lists of simple negative roots of both polynomials. In modulus coordinates, the old root lies in its window and each complementary gap contains exactly one next root. The proof selects the old roots by the intermediate value theorem or the supplied point witnesses and exhausts the old degree. It applies the shared sign-transfer theorem to the two endpoint arrays. Uniqueness identifies the resulting complete next-root lists, so their inequalities hold simultaneously. [Shared sign transfer and root-list uniqueness](../../../shared/lean/OpenMathResearch/OrientedNegativeInterlace.lean)

This is supporting Lean coverage for [issue #4](https://github.com/ProgramComputer/open-math-research/issues/4). The row degrees, analytic bounds and finite certificate signs enter as hypotheses. The computation of the witness arrays and the full permutation interlacing theorem remain outside this build.

## Related formal proofs

Bowen Zuo’s strictly positive-width criterion also finds old roots by an endpoint sign change and locates next roots in the complementary gaps. The gamma-certificate readout instead accepts checked gamma rows and their bracket ordering. The mixed criterion uses old-root point witnesses alongside strict brackets and needs only the next-row values at their endpoints. [Zuo’s `interlacing_of_brackets`](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleFinite/Interlacing.lean#L80) · [Zuo’s `original_pair_of_gamma_checks`](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleFinite/K4Readout.lean#L8)

For the connection to permutations at general cutoff, Zuo’s `actual_general_cycle_row` identifies the original enumerator with $X$ times the general quotient. The shape and reciprocity of the quotient and the transfer back to the original enumerator are also formalized upstream. [Original-row identity](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/GeneralCycleQuotient.lean#L98) · [Quotient shape](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/GeneralCycleQuotient.lean#L131) · [Quotient reciprocity](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/GeneralCycleQuotient.lean#L159) · [Interlacing transfer](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/GeneralCycleQuotient.lean#L195)

## Build and axiom audit

The research build used Lean 4.19.0 (`6caaee842e94`) and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. With the pinned mathlib build cache available, run from the repository root. [Toolchain pin](../../../shared/lean/lean-toolchain) · [Dependency manifest](../../../shared/lean/lake-manifest.json) · [Shared Lean setup](../../../shared/lean/README.md)

```sh
cd shared/lean
mkdir -p .lake/build/lib/lean/OpenMathResearch
lake env lean -o .lake/build/lib/lean/OpenMathResearch/AlternatingSignRoots.olean \
  OpenMathResearch/AlternatingSignRoots.lean
lake env lean -o .lake/build/lib/lean/OpenMathResearch/OrientedNegativeInterlace.olean \
  OpenMathResearch/OrientedNegativeInterlace.lean
lake env lean -R ../../topics/long-cycle-excedances/lean \
  -o .lake/build/lib/lean/LongCycleMixedRootWitnesses.olean \
  ../../topics/long-cycle-excedances/lean/LongCycleMixedRootWitnesses.lean
lake env lean --stdin <<'LEAN'
import LongCycleMixedRootWitnesses
#print axioms OpenMathResearch.LongCycleExcedances.interlace_of_mixed_root_witnesses
LEAN
```

All three modules compiled. The audit reported `propext`, `Classical.choice` and `Quot.sound`.
