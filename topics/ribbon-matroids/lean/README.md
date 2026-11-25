# Lean verification of the ribbon reduction

[Ribbon.lean](Ribbon.lean) verifies the graph-theoretic reduction for any finite set of noncrossing diagonals of a polygon. The vertices have cyclic labels from 0 through $n-1$, and a graph records its edges as increasing pairs. The proof establishes the two sides of any selected diagonal, shows that they share precisely its endpoints and the diagonal, and builds walks along the two boundary arcs. Each side remains connected when the diagonal is removed. In particular, the endpoints are reachable in the full graph with that edge deleted.

`polygon_eq_boundary` iterates the reduction by finite-set induction. `polygon_narayana` takes a coefficient-valued graph invariant and two explicit hypotheses. The invariant must satisfy deletion equality whenever the displayed parallel-connection conditions hold, and its value on the boundary cycle must equal the Narayana coefficient function. `fan_narayana` specializes this theorem to a hub with any subset of the allowable interior spokes. The proof constructs the parallel-connection data for each call to the deletion hypothesis.

These are conditional statements about the invariant. Instantiating them for matroid $Z$ still uses Braden and Vysogorets’s deletion identity and correction-term vanishing, and Proudfoot, Xu and Young’s cycle evaluation. Identifying a ribbon matroid with a multi-fan and passing to its simplification also remains in the mathematical proof. These identifications and the general Narayana root statement have no Lean proof in these files. [Mathematical proof](../proof.md) · [Braden–Vysogorets](https://arxiv.org/pdf/1909.09888) · [Proudfoot–Xu–Young](https://arxiv.org/pdf/1706.05575) · [Knauer–Martínez-Sandoval–Ramírez Alfonsín](https://arxiv.org/pdf/1510.00600)

[RibbonExamples.lean](RibbonExamples.lean) checks three rank-three graphs directly. They are the boundary of a quadrilateral, the quadrilateral plus one diagonal, and the latter with a parallel copy of the diagonal. For every edge subset, it computes the graphic rank by merging connected components. It then enumerates the flats and checks the full coefficient identity defining the Kazhdan–Lusztig polynomial on every contraction by a flat, including the degree bound. Its characteristic polynomial computation uses signed subsets. The $Z$-coefficient sums are computed independently of the deletion theorem. In both graphs with a diagonal, the resulting coefficient list is $[1,6,6,1]$, equal to the Narayana list for $n=4$. The diagonal deletion equality is also checked directly.

The finite computations use Lean’s kernel-checked `decide`. They do not establish a generic identification between the finite graph rank algorithm and Mathlib’s abstract matroid rank. The mathematical interpretation uses the graphic rank formula and the usual uniqueness of the Kazhdan–Lusztig recurrence.

## Library coverage and reproduction

Mathlib 4.19.0 provides abstract matroids, ranks, flats and minors. Its searched source had no matroid Kazhdan–Lusztig or $Z$-polynomial theory. The inspected RealRooted revision provides Narayana root theorems and extensive interlacing theory. Its cited uniform-matroid module concerns Hodge–Poincaré polynomials, and the searched paths did not locate ribbon or Kazhdan–Lusztig results. That revision targets Lean 4.36.0. The two local files use Mathlib 4.19.0. [RealRooted toolchain](https://github.com/PerAlexandersson/RealRooted/blob/3db7e3e484309666adfaa7dcc9b340387c156aa9/lean-toolchain) · [Narayana roots](https://github.com/PerAlexandersson/RealRooted/blob/3db7e3e484309666adfaa7dcc9b340387c156aa9/RealRooted/CombinatorialExamples/Narayana.lean) · [Uniform-matroid module](https://github.com/PerAlexandersson/RealRooted/blob/3db7e3e484309666adfaa7dcc9b340387c156aa9/RealRooted/Applications/BinderVecchi/UniformMatroid.lean)

The [shared Lean project](../../../shared/lean/README.md) pins the dependencies. From its project directory, run the topic targets.

~~~sh
lake build Ribbon RibbonExamples
~~~

The `#print axioms` lines audit the exported claims. The graph reduction uses only standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. The finite graph certificates report only `propext`.
