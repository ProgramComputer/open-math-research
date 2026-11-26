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

The declaration `BalancedEventual.exists_balanced_phase_radii` uses the exact lower and upper limits from the written proof and the internal levels $k\pi$ for $1\le k<\lfloor nr/d\rfloor$. It checks the floor comparison required at the upper limit. Its continuity and endpoint hypotheses for the actual phase are discharged below. The angular signs and geometric-to-phase joins remain outside Lean. The uniform eventual theorem still has partial formal coverage.

Use the research pins above. From the repository root, with the pinned dependencies built, run

~~~sh
cd shared/lean
lake build OpenMathResearch.FirstLevelHits
lake env lean ../../topics/balanced-arrays/eventual-all/lean/BalancedPhaseFirstHit.lean
~~~

The agent-assisted replay compiled an `.olean` into a temporary output directory with Lean 4.19.0 and the existing mathlib cache at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All five declarations use only `propext`, `Classical.choice` and `Quot.sound`. [Axiom output](phase-first-hit-axioms.txt)

## The occupied-cell phase and its endpoint limits

[BalancedOccupiedPhase.lean](BalancedOccupiedPhase.lean) constructs the two actual sums evaluated on the ray of angle $\pi/d$, for integers $1\le r<d$. The row weights are $\binom ds$. The moment weights are $\binom ds s(d-s)$, omitting the common positive factor $1/[d(d-1)]$. The two expectations in the quotient in the written phase share the row-law normalization, which cancels. The positive factor omitted from the moment weights leaves its argument unchanged.

The imaginary parts of both sums are positive at every positive radius. Each summand has nonnegative imaginary part, and the summand at size one has positive imaginary part. This places both values in the domain of the continuous principal argument. Their difference of arguments gives the quotient argument without a change of branch. The resulting phase is continuous in the logarithmic radius.

At zero, the row sum tends to one. The moment sum equals the radius times a shifted finite polynomial. Its argument tends to $\pi/d$ by continuity of the argument at that polynomial's nonzero constant term. At infinity, normalizing by the positive $r$th power of the radius gives two finite polynomials in reciprocal radius. Each has a nonzero constant term of argument $r\pi/d$. Thus the phase limits are $-((d-1)/2)(\pi/d)$ and $(nr/d)\pi$. The declaration `BalancedEventual.OccupiedPhase.exists_phase_radii` supplies the ordered first hitting radii directly for the concrete phase.

Run with the same research toolchain. After building the shared lemma above, compile the local first-hit specialization before checking the occupied phase.

~~~sh
cd shared/lean
lake build OpenMathResearch.FirstLevelHits
topic=../../topics/balanced-arrays/eventual-all/lean
lake env lean --root="$topic" -o .lake/build/lib/lean/BalancedPhaseFirstHit.olean "$topic/BalancedPhaseFirstHit.lean"
lake env lean "$topic/BalancedOccupiedPhase.lean"
~~~

The agent-assisted check uses Lean 4.19.0, compiler commit `6caaee842e94`, and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. [Axiom output](occupied-phase-axioms.txt)

## Quantitative tilt of the occupied-cell phase

[BalancedOccupiedTilt.lean](BalancedOccupiedTilt.lean) uses the actual normalized weights $\binom ds v^s/\sum_{j=0}^r\binom dj v^j$ for $v>0$ and integers $1\le r<d$. It defines the finite mean $\mu$ and variance $V$, centers the positive-weight complex sum at angle $\mu\phi$, and checks that the rotation introduces no wrap of the principal argument, where $\phi=\pi/d$.

The proof checks the real-part lower bound $1-V\phi^2/2$ and the imaginary-part bound $2V\phi^2$ for the centered sum. It then proves the unconditional estimates

$$
|\arg H(ve^{i\phi})-\mu\phi|\le 2\pi V\phi^2
$$

and

$$
|\Psi(v)/\pi-n\mu/d|\le 2nV\phi^2+(d-1)/2.
$$

This verifies the argument estimate and its contribution to the phase inequality in [the eventual proof](../proof.md#the-phase-radii). The conditional theorem `phase_deviation_le_min_mean_deficit` also checks the scalar interpolation from the three truncated-binomial variance bounds in [the published derivation](../../very-tall/proof.md), and gives the term $4\pi^2\min(y,T-y)/\sqrt d$ with $y=n\mu/d$ and $T=nr/d$. The next formal obligations are the bounds $V\le d/4$, $V\le\mu(1+\mu)$ and $V\le(r-\mu)(1+r-\mu)$ for these finite probabilities. The angular signs and mixed radius joins are separate.

The published variance derivation uses two inputs. Conditioning an exchangeable coordinate on success or failure gives the same $(d-1)$-trial tilted law truncated at $r-1$ or $r$, respectively. The former mean is no larger, so the conditional difference in total size is at most one. The tail argument uses the decreasing ratios of the positive masses of $S$ and $r-S$. For their survival probabilities $F_j$ and masses $p_j$, the ratio $F_j/p_j$ is a sum of successive products of those ratios and decreases. Hence $F_{i+j}\le F_iF_j$, which bounds the second factorial moment by twice the squared mean. These two arguments have been checked on paper and are the hypotheses left open in the conditional Lean theorem.

Use the research pins above. Compile the shared first-hit module, topic specialization and concrete phase before checking the tilt module.

~~~sh
cd shared/lean
lake build OpenMathResearch.FirstLevelHits Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
topic=../../topics/balanced-arrays/eventual-all/lean
lake env lean --root="$topic" -o .lake/build/lib/lean/BalancedPhaseFirstHit.olean "$topic/BalancedPhaseFirstHit.lean"
lake env lean --root="$topic" -o .lake/build/lib/lean/BalancedOccupiedPhase.olean "$topic/BalancedOccupiedPhase.lean"
lake env lean "$topic/BalancedOccupiedTilt.lean"
~~~

The local replay uses Lean 4.19.0, compiler commit `6caaee842e94`, and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. [Axiom output](occupied-tilt-axioms.txt)
