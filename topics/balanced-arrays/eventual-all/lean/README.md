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
lake build BalancedNoFullRowCounting
lake env lean ../../topics/balanced-arrays/eventual-all/lean/BalancedEventual.lean
~~~

The verifier compiled both files with these pins and an existing macOS dependency cache. The orchestrator then compiled the repository copies in a fresh temporary output directory. Both runs produced the same nine axiom reports. Each lists only `propext`, `Classical.choice`, and `Quot.sound`. The exact compiler output is included. The publication toolchain is Lean 4.36.0 with mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. A stable port has yet to be checked. [Axiom output](axioms.txt)

## Open proof obligation

The existing [alternating-sign mesh theorem](../../../../shared/lean/OpenMathResearch/AlternatingSignRoots.lean) produces a complete list of real roots from ordered sign samples. Its remaining interface to the complex root predicate must show that $`D`$ disjoint negative intervals with endpoint sign changes force exactly $`D`$ simple negative complex roots for a real polynomial of degree $`D`$. Applied to the checked degree, this leaves the uniform construction of an ordered alternating sign sequence. The paper builds that sequence from finite-dimension, large-dimension, and analytic sector estimates. Those estimates and the uniform root theorem have no Lean proof in this development. There is no independent kernel replay or full verification claim.
