# Lean verification of the ribbon reduction

[Ribbon.lean](Ribbon.lean) verifies the graph-theoretic reduction for any finite set of noncrossing diagonals of a polygon. The vertices have cyclic labels from 0 through $n-1$, and a graph records its edges as increasing pairs. The proof establishes the two sides of any selected diagonal, shows that they share precisely its endpoints and the diagonal, and builds walks along the two boundary arcs. Each side remains connected when the diagonal is removed. In particular, the endpoints are reachable in the full graph with that edge deleted.

`polygon_eq_boundary` iterates the reduction by finite-set induction. `polygon_narayana` takes a coefficient-valued graph invariant and two explicit hypotheses. The invariant must satisfy deletion equality whenever the displayed parallel-connection conditions hold, and its value on the boundary cycle must equal the Narayana coefficient function. `fan_narayana` specializes this theorem to a hub with any subset of the allowable interior spokes. The proof constructs the parallel-connection data for each call to the deletion hypothesis.

These are conditional statements about the invariant. Instantiating them for matroid $Z$ still uses Braden and Vysogorets’s deletion identity and correction-term vanishing, and Proudfoot, Xu and Young’s cycle evaluation. Identifying a ribbon matroid with a multi-fan and passing to its simplification also remains in the mathematical proof. These identifications and the general Narayana root statement have no Lean proof in these files. [Mathematical proof](../proof.md) · [Braden–Vysogorets](https://arxiv.org/pdf/1909.09888) · [Proudfoot–Xu–Young](https://arxiv.org/pdf/1706.05575) · [Knauer–Martínez-Sandoval–Ramírez Alfonsín](https://arxiv.org/pdf/1510.00600)

[RibbonExamples.lean](RibbonExamples.lean) checks three rank-three graphs directly. They are the boundary of a quadrilateral, the quadrilateral plus one diagonal, and the latter with a parallel copy of the diagonal. For every edge subset, it computes the graphic rank by merging connected components. It then enumerates the flats and checks the full coefficient identity defining the Kazhdan–Lusztig polynomial on every contraction by a flat, including the degree bound. Its characteristic polynomial computation uses signed subsets. The $Z$-coefficient sums are computed independently of the deletion theorem. In both graphs with a diagonal, the resulting coefficient list is $[1,6,6,1]$, equal to the Narayana list for $n=4$. The diagonal deletion equality is also checked directly.

The finite computations use Lean’s kernel-checked `decide`. They do not establish a generic identification between the finite graph rank algorithm and Mathlib’s abstract matroid rank. The mathematical interpretation uses the graphic rank formula and the usual uniqueness of the Kazhdan–Lusztig recurrence.

## Kazhdan–Lusztig and Z-polynomial definitions

The stable Lean sources construct the integer Kazhdan–Lusztig coefficient family on the ranked poset of actual Mathlib matroid flats. The construction recurses on interval rank. Lean checks its uniqueness under the degree bound and palindromicity, and uses incidence-algebra convolution to prove the equivalence with the characteristic-polynomial recurrence. [Coefficient construction](../../../shared/lean/OpenMathResearch/MatroidKL.lean) · [Recurrence comparison](../../../shared/lean/OpenMathResearch/MatroidKLRecurrence.lean) · [Proudfoot–Xu–Young, §2](https://doi.org/10.37236/7105)

Adjoining a contracted flat identifies the flat poset of the actual Mathlib contraction with the corresponding upper interval and shifts rank by the rank of that flat. Lean checks the original characteristic-polynomial recurrence for `matroidKL` and the definition of `matroidZ` as the rank-shifted sum of the Kazhdan–Lusztig polynomials of all the contractions. The rank-zero value is $1$. [Matroid-flat model](../../../shared/lean/OpenMathResearch/MatroidFlatPolynomial.lean) · [Contraction and matroid-level recurrence](../../../shared/lean/OpenMathResearch/MatroidFlatContract.lean)

The separate statement `Ribbon.Source.NarayanaClaim` specifies the nonempty connected ribbons by boundary-step words, bases between their north-prefix bounds and exclusion of a $2\times2$ block of cells. It asks for every Narayana coefficient and for every complex zero of $Z$ to have zero imaginary part. Lean proves that the north-step count in the boundary is the matroid rank. If the empty rank-zero convention is admitted, `matroidZ_of_rank_zero` gives its value $N_1=1$. [Source-facing Lean statement](publication/RibbonNarayanaSpec.lean) · [SymCat statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsGraphs)

Lean identifies the cells of the strip from the two north-prefix counts. The no-square condition bounds their difference by one. Connectedness supplies a circuit across each interior cut, whose basis exchange forces the difference to be positive. Hence the boundaries take the same interior steps. Lean then constructs the ordered union of their north-step positions and proves that the original matroid bases are exactly the sets of distinct representatives of the successive closed intervals. [Boundary proof](publication/RibbonBoundaryProfile.lean) · [Interval-transversal basis proof](publication/RibbonChainPresentation.lean)

The direct-sum proof identifies the product of the flat posets and uses the rank and degree bounds to prove `tau_sum_eq_zero` for two finite matroids of positive rank. This checks the coefficient vanishing used in the paper proof whenever the contraction has the required direct-sum form. [Product of ranked intervals](../../../shared/lean/OpenMathResearch/MatroidKLProduct.lean) · [Direct sums of matroids](../../../shared/lean/OpenMathResearch/MatroidFlatSum.lean) · [Braden–Vysogorets, Lemma 2.7](https://arxiv.org/pdf/1909.09888)

For a finite matroid whose complement of an element spans, `matroidZ_delete_of_tau_zero` proves that deletion preserves $Z$ if the top Kazhdan–Lusztig coefficient vanishes for each required contraction. The proof sends centered coefficients along the map of deletion flats and compares their constants. `matroidZ_delete_of_parallel` uses the same theorem to delete a parallel copy. [Centered coefficients](../../../shared/lean/OpenMathResearch/MatroidKLDeletionProfile.lean) · [Matroid deletion](../../../shared/lean/OpenMathResearch/MatroidFlatDelete.lean) · [Braden–Vysogorets, equation (6)](https://arxiv.org/pdf/1909.09888)

For an interior element of the interval presentation, Lean constructs bases of its contraction by splicing interval choices across the cut. The two sides split as a direct sum, and independent chains on either side force both ranks to be positive after the further contractions in the deletion identity. The checked deletion therefore preserves $Z$. Repeating over all nonseparator elements leaves exactly the boundary separators. Every basis there omits exactly one separator. The result `Ribbon.Source.IsRibbonPresentation.exists_circuitBoundary` starts from the original source-facing ribbon presentation. [Interior deletion and contraction](publication/RibbonChainDeletion.lean) · [Boundary circuit](publication/RibbonChainBoundary.lean)

The rank layers of each proper flat of a circuit matroid are counted by subsets of the remaining ground elements. Lean verifies the integer binomial convolution for the circuit’s $Z$-polynomial, proves that the candidate satisfies the unique Kazhdan–Lusztig recursion, and transfers every Narayana coefficient back to the original ribbon. [Circuit-flat counts](publication/CircuitNarayanaMatroid.lean) · [Binomial calculation](publication/CircuitNarayanaCoefficients.lean) · [Original coefficient equality](publication/RibbonNarayanaCoefficients.lean)

Coverage remains 🟨 Partial. The outstanding formal obligation is the root conclusion. [Verification record](../verification.json) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/133)

To build and audit this foundation, use Lean 4.36.0 and the [shared manifest](../../../shared/lean/publication/lake-manifest.json) with mathlib at `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Run from the repository root.

~~~sh
build_dir=$(mktemp -d)
python3 shared/lean/publication/prepare.py ribbon-foundation "$build_dir"
(
  cd "$build_dir"
  lean --version
  lake exe cache get $(cat cache-imports.txt)
  test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = fc4f59e577feb1a4956671bc04ac18aaaf8cd842
  lake build $(cat targets.txt)
)
python3 shared/lean/publication/audit_axioms.py ribbon-foundation "$build_dir"
~~~

## Library coverage and reproduction

Mathlib 4.19.0 provides abstract matroids, ranks, flats and minors. Its searched source had no matroid Kazhdan–Lusztig or $Z$-polynomial theory. The inspected RealRooted revision provides Narayana root theorems and extensive interlacing theory. Its cited uniform-matroid module concerns Hodge–Poincaré polynomials, and the searched paths did not locate ribbon or Kazhdan–Lusztig results. That revision targets Lean 4.36.0. The two local files use Mathlib 4.19.0. [RealRooted toolchain](https://github.com/PerAlexandersson/RealRooted/blob/3db7e3e484309666adfaa7dcc9b340387c156aa9/lean-toolchain) · [Narayana roots](https://github.com/PerAlexandersson/RealRooted/blob/3db7e3e484309666adfaa7dcc9b340387c156aa9/RealRooted/CombinatorialExamples/Narayana.lean) · [Uniform-matroid module](https://github.com/PerAlexandersson/RealRooted/blob/3db7e3e484309666adfaa7dcc9b340387c156aa9/RealRooted/Applications/BinderVecchi/UniformMatroid.lean)

The [shared Lean project](../../../shared/lean/README.md) pins the dependencies. From its project directory, run the topic targets.

~~~sh
lake build Ribbon RibbonExamples
~~~

The `#print axioms` lines audit the exported claims. The graph reduction uses only standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. The finite graph certificates report only `propext`.
