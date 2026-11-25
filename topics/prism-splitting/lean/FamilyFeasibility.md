# Direct reciprocity for the infinite prism family

The Lean proof goes from the geometric lattice counts to the two leading coefficients and the final [noninterlacing theorem](PrismFamilyInterlacing.lean). The family is at level $a=b+1$ with $b\ge6$. The bound vectors are $(1^{2b},2)$ and $(1^{2b+2})$. For either vector let $m$ be its number of coordinates and let $D=m-1$. The existing affine dimension argument applies because the bounds are positive and sum to $2a$. [Affine dimension theorem](PrismDimensions.lean)

## Extend the closed count to integer arguments

For $J$ a subset of the coordinate indices, write $C(J)=\sum_{j\in J}c_j$ and $e=|J|$. Define an integer-valued function on $q\in\mathbb Z$ by

$$
F(q)=\sum_{C(J)<a}(-1)^e\binom{(a-C(J))q+D-e}{D},
$$

using the generalized integer binomial coefficient for negative top arguments. For $q\ge0$ this is the closed lattice count. To see this, expand the coefficient of $z^{aq}$ in

$$
\frac{\prod_i(1-z^{q c_i+1})}{(1-z)^m}.
$$

If $C(J)\ge a$ the shifted exponent is negative because $e>0$. Otherwise $e\le C(J)\le a-1$, so the binomial top entry is nonnegative, even when the shifted exponent is negative. The usual zero convention then gives the correct coefficient. In the two families, the subset sum groups by the number of selected unit bounds and by whether the exceptional bound is selected.

Each term has vanishing $(D+1)$st forward difference on $\mathbb Z$. The first difference of $q\mapsto\binom{s q+u}{D+1}$ is the sum of the $s$ functions $q\mapsto\binom{s q+u+i}{D}$ for $0\le i<s$, by Pascal's identity. This also proves polynomiality of the normalized count series on $\mathbb N$, using the same coefficient argument as [the finite proof](PrismSeriesClosure.lean).

For $r\ge1$ and $r\le m$, the $m$th forward difference of $F$ at $-r$ is zero. Its terms with nonnegative arguments are exactly the coefficient $h_{m-r}$ of the normalized count series. Moving the remaining $r$ terms to the other side gives

$$
h_{m-r}=-\sum_{i=0}^{r-1}(-1)^{m-i}\binom mi F(-(r-i)).
$$

This is the finite-difference identity used by the Lean proof. [Integer count extension](PrismFamilyCounts.lean) · [Coefficient reflection](PrismFamilyTop.lean)

## Reflect the count and read the top coefficients

Generalized binomial reflection at $q=-r$, for $r\ge1$, changes the summand in $F$ according to

$$
(-1)^D\binom{-(a-C(J))r+D-e}{D}
=\binom{(a-C(J))r+e-1}{D}.
$$

For $r\ge2$, this is exactly the inclusion–exclusion term for the strict lattice bounds $0<x_i<r c_i$. Shift each coordinate down by one. The resulting caps are $r c_i-2$, and the target sum is $ra-m$. The shifted exponent is $(a-C(J))r-(m-e)$. It is negative if $C(J)\ge a$. In the only possible borderline case $e=m$, the weight is $C(J)=2a>a$, so the exponent is still negative. For $r=1$, each retained binomial term has a top entry at most $a-1<D$ and is zero. The strict first dilation also has count zero since each vector has unit bounds.

Write $I(r)$ for these strict-bound counts. Substituting $I(r)=(-1)^D F(-r)$ into the coefficient identity gives

$$
h_{m-r}=\sum_{i=0}^{r-1}(-1)^i\binom mi I(r-i).
$$

The first three equalities give $h_D=0$, $h_{D-1}=1$, and $h_{D-2}=I(3)-m$. Here $I(1)=0$ and $I(2)=1$. In dilation two the unit coordinates must equal one. The exceptional coordinate in the unsplit box is then forced to two. In dilation three the split count is $\binom{2b+2}{b+1}$. For the unsplit count the number of unit coordinates equal to two can be any of $b-2,b-1,b,b+1,b+2$, with the exceptional coordinate uniquely determined. These two next coefficients differ by more than one. [Direct reciprocity](PrismFamilyReciprocity.lean) · [Top coefficients](PrismFamilyTop.lean)

## Rule out interlacing

For the all-unit box, $I(r)=F(r-2)$ at $r\ge2$ by translation, so its numerator is reciprocal. At $0<x<1$ it is positive because the closed counts are nonnegative and the zeroth count is one. Lean uses the convergent binomial generating series to relate that positive sum to polynomial evaluation. Reciprocity excludes roots greater than one. Under weak alternation, the difference of the negated sums of the roots can be at most the largest split root, hence at most one. Vieta gives the contradiction. [Root bound and interlacing theorem](PrismFamilyInterlacing.lean)

## Verify both parameter ranges

For $a=6$ use the concrete theorem <code>PrismSplit.finBoxSplitCounterexample</code>. For each $a\ge7$, set $b=a-1$ and use <code>PrismFamily.familyBoxSplitCounterexample</code>. The family theorem identifies the actual finite-coordinate box slices, their affine dimensions, and their integer counts in geometric dilations. Its interlacing predicate lists the real roots with multiplicity and requires both polynomials to split over the reals. The proof has no additional hypotheses on their roots. [Concrete case](Dimensions.md) · [Family geometry](PrismFamilyGeometry.lean)

After the [shared dependency and cache setup](../../../shared/lean/README.md), run from the shared Lean project:

~~~sh
export LEAN_NUM_THREADS=1
lake build PrismDimensions PrismFamilyInterlacing
~~~

The principal family theorems were checked serially with Lean and mathlib 4.19.0. They depend only on <code>propext</code>, <code>Classical.choice</code>, and <code>Quot.sound</code>. [Source digests and axiom reports](../verification.json)
