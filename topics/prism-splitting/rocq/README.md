# The prism-slice splitting disproof in Rocq

**🟩 Full · Rocq.** For every integer $a\ge6$, splitting the final bound of $(1^{2a-2},2)$ at level $a$ into two unit bounds gives Ehrhart numerators that fail to interlace. The theorem excludes weak interlacing in both orientations, including repeated roots. [Original conjecture, §5](https://doi.org/10.4153/S0008414X24000233) · [Written disproof](../paper.pdf) · [Rocq family theorem](PrismFamily.v)

## From geometric slices to Ehrhart numerators

Write $b=a-1$. Each slice has an affine chart with $n$ freely chosen coordinates and last coordinate $a-\sum_i x_i$, where $n=2b$ before the split and $n=2b+1$ afterwards. The hull of the bounded slice is the entire hyperplane. An explicit affine extrapolation proves this from its center. For every integer dilation $t\ge0$, including zero, the signed lattice points of that geometric dilation correspond to the enumerated coordinate lists. Rocq proves exact membership, absence of duplicates, and equality of the length with the counting recurrence. [Affine chart and signed lattice points](PrismAffine.v) · [Enumeration](../../../shared/rocq/BoundedCompositions.v)

Rocq multiplies each lattice-count series by $(1-z)^{n+1}$ using integer finite differences. It proves the resulting coefficient list is exact at every index. Reflection of the rising factorial recovers the top coefficients from strict interior counts. Both numerators are monic. [Reciprocity](../../../shared/rocq/BoxReflection.v) · [Finite numerator and top coefficients](../../../shared/rocq/NumeratorTable.v)

## Two root arguments

- At $a=6$, two distinct real zeros of the split numerator lie in $(-840,-838)$ and $(-57,-56)$. A Bernstein expansion proves that the other numerator is positive between them. Every alternating pair would have a zero between those two. [Exact vectors and series](PrismEndpoint.v) · [Root certificates](PrismDisproof.v)
- For $a\ge7$, write $p$ and $q$ for the next-to-leading coefficients before and after splitting. Integer counts at dilation three give $p>q+1$. Reflection and a finite summation-by-parts argument show that every real root of the split numerator is at most one. Under interlacing, Vieta’s formula and the ordering of the root lists would give $p\le q+1$. The factorization definition permits any nonzero scalar, either orientation and ties. [Interior-count gap](PrismFamilyCounts.v) · [Positivity proof](../../../shared/rocq/PositiveSeries.v) · [Vieta and weak alternation](../../../shared/rocq/MonicRoots.v)

The combined theorem is `geometric_prism_family`. Its sole hypothesis is $a\ge6$. The theorem `family_affine_charts` also supplies the affine chart and its inverse explicitly. [Family theorem](PrismFamily.v) · [Affine chart](PrismAffine.v)

## Reproduce the verification

Use Rocq 9.3.0 with its standard library. Run from the repository root.

~~~sh
topics/prism-splitting/rocq/verify.sh
~~~

The script builds all modules in a fresh temporary directory, prints the assumptions of the audited theorems, and runs `rocq check` on the family theorem and its dependencies. The verification record gives the assumptions for each named theorem, the source hashes, and the output of the clean run. [Audit declarations](Audit.v) · [Verification record](verification.json)
