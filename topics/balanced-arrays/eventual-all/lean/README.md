# Balanced arrays formal verification

This research-branch verification concerns the reviewed uniform eventual theorem tracked in [research issue #2](https://github.com/ProgramComputer/open-math-research/issues/2). The public research checkout used for comparison was at commit `4dad276e21cf4e8040053675fc0dd331f410f7d7`.

## Specification

Per Alexandersson's original conjecture in SymCat asks for the real-rootedness of the polynomial whose coefficient at degree $`k`$ counts labeled $`n\times d`$ binary arrays with every column sum $`k`$ and every row sum at most $`r`$, for all $`n\ge 0`$ and $`1\le r\le d`$. It asks for real-rootedness with multiplicity allowed. [Primary source](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

The reviewed partial theorem gives a single absolute threshold $`N`$. For every $`n\ge N`$, $`d\ge2`$, and $`1\le r\le d`$, the polynomial has precisely $`\lfloor nr/d\rfloor`$ distinct, strictly negative real roots. For $`d=1`$ the polynomial equals $`(1+q)^n`$ for every $`n`$. The theorem leaves the original claim for $`n<N`$ open, subject to other established cases. [Statement and review links](https://github.com/ProgramComputer/open-math-research/blob/4dad276e21cf4e8040053675fc0dd331f410f7d7/topics/balanced-arrays/eventual-all/README.md)

The separately specified `OriginalClaim` requires the imaginary part of every complex root to vanish. `EventualClaim` puts the row threshold outside the universal quantifiers for rows, dimension, and cap. Its root predicate quantifies over an injective indexing by `Fin (n * r / d)`, explicitly states negativity and derivative nonvanishing, and identifies the range with the complete complex root set. Both claims are definitions of propositions.

## Checked declarations

[BalancedEventual.lean](BalancedEventual.lean) starts from the existing `BinaryArray` type, with labels given by `Fin n` and `Fin d`, and adds arbitrary caps. The corank-one bridge identifies the counting sets with those of the existing development. The double counting proof bounds the number of cells equal to one by $`nr`$. The cyclic construction assigns the $`dk`$ positions from $`0`$ through $`dk-1`$ to rows by their residues modulo $`n`$. Each block of $`k`$ positions uses $`k`$ distinct rows in its column. For any row, distinct occupied columns inject into the $`r`$ possible quotients by $`n`$. This proves nonemptiness at every $`k`$ in the stated support. The coefficient identity connects the finite Lean polynomial with the original counts, including exponents outside its summation range. Together these facts give the exact degree. A bijection with $`k`$-element subsets of the labeled rows also proves the dimension-one identity.

## Reproduction

The research build uses Lean 4.19.0 (compiler commit `6caaee842e94`) and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. From the repository root, the shared Lake project supplies the exact dependencies and the existing labeled-array module. [Toolchain](../../../../shared/lean/lean-toolchain) · [Dependency manifest](../../../../shared/lean/lake-manifest.json)

~~~sh
cd shared/lean
lake build BalancedNoFullRowCounting OpenMathResearch.AlternatingSignRoots
topic=../../topics/balanced-arrays/eventual-all/lean
lake env lean --root="$topic" -o .lake/build/lib/lean/BalancedEventual.olean "$topic/BalancedEventual.lean"
lake env lean "$topic/BalancedEventualSigns.lean"
~~~

The verifier compiled the foundation and the sign reduction with these pins and an existing macOS dependency cache. The orchestrator then compiled both repository files, the corank-one input and the shared alternating-sign module in a fresh temporary output directory. The final replay uses the shared module under its repository name. All 14 audited declarations list only `propext`, `Classical.choice`, and `Quot.sound`. The publication toolchain is Lean 4.36.0 with mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. A stable port has yet to be checked. [Axiom output](axioms.txt)

## From signs to all complex roots

The [sign reduction](BalancedEventualSigns.lean) applies the existing [alternating-sign mesh theorem](../../../../shared/lean/OpenMathResearch/AlternatingSignRoots.lean) to the real polynomial counted from the labeled arrays. It transfers the entire real root multiset to the complex polynomial and proves the derivative is nonzero at every root. It also covers degree zero. Together these yield the checked conditional theorem `eventualClaim_of_alternating_sign_mesh`.

**Outstanding obligation.** Prove `EventualAlternatingSignMesh`: one absolute row threshold must provide the complete ordered sequence of alternating signs for every admissible dimension and cap in positive degree. The uniform estimates which construct those signs remain outside Lean. The eventual theorem itself still has partial formal coverage.

## Ordered first hits for the phase radii

[BalancedPhaseFirstHit.lean](BalancedPhaseFirstHit.lean), using the shared [first-hit lemma](../../../../shared/lean/OpenMathResearch/FirstLevelHits.lean), verifies the first-hit step in [The phase radii](../proof.md#the-phase-radii). For a continuous real phase in logarithmic radius with limits below and above a specified level, it constructs the least point attaining that level. The intermediate value theorem gives a hit in a compact interval, and the lower-tail hypothesis excludes earlier hits. Applying the intermediate value theorem before the first hit of a higher level proves strict ordering of the first hits. The exponential map transfers the construction to positive radii.

The declaration `BalancedEventual.exists_balanced_phase_radii` uses the exact lower and upper limits from the written proof and the internal levels $k\pi$ for $1\le k<\lfloor nr/d\rfloor$. It checks the floor comparison required at the upper limit. It assumes continuity and the two limits for the actual phase. The next formal obligation is to define the occupied-cell phase from the two finite tilted row-size sums, show their arguments stay in the stated sectors, and prove continuity and both endpoint limits. The angular signs and geometric-to-phase joins also remain outside Lean. The uniform eventual theorem still has partial formal coverage.

Use the research pins above. From the repository root, with the pinned dependencies built, run

~~~sh
cd shared/lean
lake build OpenMathResearch.FirstLevelHits
lake env lean ../../topics/balanced-arrays/eventual-all/lean/BalancedPhaseFirstHit.lean
~~~

The agent-assisted replay compiled an `.olean` into a temporary output directory with Lean 4.19.0 and the existing mathlib cache at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All five declarations use only `propext`, `Classical.choice` and `Quot.sound`. [Axiom output](phase-first-hit-axioms.txt)
