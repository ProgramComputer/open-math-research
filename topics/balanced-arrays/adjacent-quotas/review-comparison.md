# Independent audit of adjacent-quota profile comparison

**Verdict.** The proof in [comparison.md](comparison.md) establishes the stated correction-slope bound whenever $`n\ge10^{200}`$, $`n/4\le d\le n`$, and both feasible consecutive densities lie in $`[.30,.70]`$. It estimates the ratio for the actual balanced-array coefficient, including at saturation. I checked its fixed-profile Fourier inputs from [the fixed-profile proof](fixed-profile.md). There is one gauge-label correction below, with no change to the estimates. This review does not independently referee the scalar bound in scalar.md.

## Gaussian input and chart estimates

For the homogeneous Gaussian edge field one can compute the moments in either of two gauges. In the gauge with column angles summing to zero, the centered Gaussian splits into independent row variables of variances $`1/(dv_i)`$ and column variables of covariance $`(I-\mathbf1\mathbf1^{\mathsf T}/d)/A`$. This gives the displayed edge covariance

$$
c_{ij,kl}=\frac{\delta_{ik}}{dv_i}+\frac{\delta_{jl}-1/d}{A}.
$$

The current text of cubic-direct.md puts that formula immediately after discussing the weighted-zero row gauge. The two gauges produce the same edge law. The formula is immediate in the zero-column-sum gauge and its derivation should say so. The weighted-zero row gauge remains valid for the later homogeneous computation.

I recomputed the determinant with one column angle fixed. Its row block is $`\mathrm{diag}(dv_i)`$ and the Schur complement in the column coordinates is $`A(I-\mathbf1\mathbf1^{\mathsf T}/d)`$, whose determinant is $`A^{d-1}/d`$. This gives the joint Gaussian factor asserted in the note. The projection cube sum in the homogeneous calculation is $`(n^2+d^2-1)/(ndv^3)`$. For example, expanding the column-centered formula gives the row cubes $`n/d`$, the column cubes $`(d-1)(d-2)/(dn)`$, and the surviving mixed term $`3(d-1)/(dn)`$, together divided by $`v^3`$. The linear Wick term is essential and has the stated sum $`nd/v`$. The homogeneous cubic variance is at most $`109/63`$, and the homogeneous quartic expectation at most $`25/16`$.

Using $`|c|\le5H`$, $`|c-c_0|\le25\eta H`$, the change in the pure cubic Wick contribution is at most

$$
\frac{54\eta}{6}\left(\frac{125}{2}+\frac{1875}{16}\right)<1620\eta .
$$

For the linear contribution, the change of the product of the two $`B_i`$ factors is bounded by $`2(7.5)(70)\eta/n^2`$, and the other contribution uses $`|B_i|\le7.5/n`$. Multiplying by $`\sum H=3nd`$ and the Wick factor $`1/4`$ gives less than $`5025\eta`$. The quartic expectation change is less than $`400\eta`$ by summing the stated $`150\eta/n`$ variance-entry bound. The quartic variance bound follows from $`c^4\le(30/n)^2c^2`$, $`\sum c^2\le225n`$ and $`a_i\le1/192`$. In fact these bounds give less than $`528/n`$. Hence the positive lower value $`1/72-\sqrt{1000/n}`$ for the Gaussian real correction is valid.

The chart is compatible with the gauge $`\theta_d=0`$. Its small cube is contained in the central set and its edges have real representatives of magnitude at most $`3\epsilon`$. The gauge variables on the cube can be recovered as $`\phi_i=X_{id}`$ and $`\theta_j=X_{1j}-X_{1d}`$, so the claimed Gaussian chart loss follows by a union bound with variance upper bound $`120/n`$. There is no overcount of wrapped charts. Outside alignment, the Bessel majorant retains the Gaussian determinant normalization. The von Mises angle bounds yield the exponents $`n\epsilon^2/120`$ for column spread and $`n\epsilon^2/200`$ for a distant row, as claimed. I checked the analytic disk for the Bernoulli log expansion, its cubic and quartic signs, the order-five and even order-six remainders, and the Gaussian moment estimate leading to $`2\cdot10^8/\sqrt n`$. At $`n\ge10^{200}`$ each remaining exponential chart or torus error is at most $`1/\sqrt n`$. Thus the signed Gaussian-correction lower bound and the absolute expansion error used in comparison.md both follow.

## Regular-profile stability

In the column-centered Gaussian representation the cubic separates into three terms by $`\sum_j T_j=0`$. The coefficient and factor estimates are valid on $`[1/4,3/4]^n`$. More explicitly, the respective changes before division by six are at most $`100s\sqrt{60}`$, $`6(30+600)s`$, and $`100s\sqrt6`$ in $`L^1`$, so their sum divided by six is below $`1000s`$. The middle product uses independence of the row and column Gaussian families, and only the first moment of the nonnegative sum of column squares is needed. The last variance bound uses zero row sums of the Gaussian column projection, which removes the linear Wick term. For the quartic estimate, Hölder with the stated $`L^4`$ bounds gives at most $`4\cdot10^5s/n^2`$ per unweighted monomial. The variation in the weight adds at most $`10^4s/n^2`$. Summing proves the claimed $`10^6s`$ bound. The Lipschitz comparison of the expectations follows.

The conditional scalar law is a product of log-concave row-size weights conditioned on the sum. Increasing the total by one gives both the direct stochastic order in the last coordinate and its reverse after subtracting one from the larger-total coordinate. The latter is equivalently the stochastic increase in the remaining total. Common quantiles make the two orders hold simultaneously, including at finite supports, and induction then couples all coordinates monotonically. After $`d`$ such steps, the sum of changes in the $`p_i`$ is exactly one. On joint regularity, centering by the changing density adds at most one to the sum of absolute changes. Each centered displacement has magnitude at most $`\eta`$, yielding $`|B'-B|\le4\eta`$ and the stated variance prefactor error.

The Robbins correction has absolute error $`1/(144m^2)`$ because its lower exponent is $`1/(12m+1)`$. With $`\ell_i,d-\ell_i\ge d/4`$ its row contributions indeed sum with total error at most $`n/d^2`$. Differentiating $`v^{-1}`$ on $`[1/4,3/4]`$ proves the stated comparison of that prefactor. The lower bound $`1/100`$ on the final factor justifies the comparison of its logarithm. All three errors are well below $`10^{-8}`$ at the given cutoff.

## Removing atypical profiles

The scalar tilt is binomial reweighted by a geometric factor and cut off above the cap. Relative to a binomial of the matching mean, its likelihood ratio has interval superlevel sets. Its signed mass difference has the minus-plus-minus pattern, so matching mass and mean give the claimed convex order by the chord test. At exact saturation the tilt is the deterministic row size and the same convex-order inequality follows directly from Jensen. The sum of independent tilted row sizes has interval log-concavity. Jensen on the concave interpolation of the log mass gives the mean value at least the mean logarithmic mass, which is at least $`-\log(nd+1)`$ by entropy. Thus the conditioning cost in the scalar tail and second moment is valid also at the endpoint.

The actual-array tail can be proved without transferring a bound through the equality event. Fix all but a specified pair of rows and let each column's residual quota be zero, one, or two. Columns with residual two force a cell in both rows. If there are $`b`$ residual-one columns, the choice for the first row is uniform over subsets of those columns constrained by the two caps. Its cardinality is $`\mathrm{Bin}(b,1/2)`$ conditioned to a symmetric central integer interval, because both rows have the same forced contribution and cap. The row-size difference is $`2Y-b`$. Conditioning on that central interval removes only more extreme outcomes and therefore cannot increase a tail probability of $`|2Y-b|`$. Hoeffding's bound is at most $`2e^{-d\eta^2/2}`$ as $`b\le d`$, with $`b=0`$ immediate. Every row profile with a deviation larger than $`d\eta`$ has a pair differing by more than $`d\eta`$, by the exact mean. The union bound proves $`t'`$. This condition is handled entirely under the uniform actual-array law.

The regular-profile upper bound implies $`H^2\le e^{200+20B}`$. Integrating the single-row Hoeffding tail yields $`\mathbb E e^{20Y^2}\le1+40/(2d-20)`$, and the product over $`n`$ rows costs less than $`e^{300}`$ here. Conditioning gives the claimed second-moment bound. The bad contribution where the profile itself is irregular is relative to its own $`W`$ via the actual-array law. Where only its partner is irregular, Cauchy–Schwarz under the scalar coupling gives exactly the asserted absolute bound. Dividing by $`W\ge1/400`$ makes the combined relative loss less than $`10^{-8}`$ on both sides. Joint regularity thus compares the integrals by the pointwise multiplicative estimate, and restoring the discarded pieces changes either logarithm by at most $`2\cdot10^{-8}`$. This proves the claimed $`10^{-6}`$ bound with room.

## Explicit endpoint and closure of feasibility

The smaller endpoint $`n=10^{200}`$ gives $`\eta=n^{-1/4}\le10^{-50}`$,
$`n^{1/5}\ge10^{40}`$ and $`\sqrt n\ge10^{100}`$. The logarithmic factors in
the chart and exceptional-profile estimates are dominated at this endpoint:
for example, both $`n^{1/5}/3840`$ and $`\sqrt n/8`$ are larger than
$`10\log n+600`$. The ratios of a positive power of $`n`$ to that logarithmic
bound increase thereafter. The regular-profile log error is bounded by
$`150\eta+32/n+100(3\cdot10^8\eta+6\cdot10^8/\sqrt n)`$, which is below
$`10^{-8}`$ already at this endpoint. All hypotheses of the fixed-profile
input are also satisfied at $`10^{200}`$.

The prior near-saturation strip is unnecessary in the final join.
At any difficult internal quota $`\Gamma_k\le4`$, the orientation
localization from the scalar note puts $`k`$ in $`(.305n,.695n)`$.
The two immediate adjacent pairs are feasible and have densities in
$`[.30,.70]`$. This holds even when the larger neighbor is saturated.
Apply the adjacent-profile comparison on those two edges only. After
subtracting the two balancing-factor contributions, the scalar
curvature satisfies

$$
\log\frac{U_k^2}{U_{k-1}U_{k+1}}
\le \log 4+2\cdot10^{-6}+50/n<1.4.
$$

Here the $`50/n`$ bounds the baseline density-curvature loss, and the
$`\sqrt d`$ in the normalization cancels between three points. The
scalar negative-binomial bound from the existing deficit result gives
the lower bound $`(n-1)/[(h+1)(h+5)]`$ at every feasible internal quota,
with $`h=nr/d-k\ge1`$. If $`h\le.84\sqrt n`$, this would exceed $`1.4`$:
indeed it is at least
$`(1-1/n)/(.84+5/\sqrt n)^2`$, which is larger than $`1.4`$ at
$`n=10^{200}`$ and improves as $`n`$ increases. Thus $`h>.84\sqrt n`$.
In particular $`h>.4\sqrt{n/\log n}`$ and $`k+3\le D`$. The left third
neighbor exists by the density localization. All four adjacent pairs
from $`k-2`$ through $`k+2`$ are now feasible and in the comparison window,
so its conclusion supplies the required four slopes. This verifies the
feasibility argument that feeds into scalar.md. The proof of the scalar
neighbor-variation estimate is outside the independent scope of this
review.

The revised fixed-profile proof now uses the zero-column-sum gauge in the covariance derivation.

**Signed** · four_central, independent agent-assisted mathematical review.
