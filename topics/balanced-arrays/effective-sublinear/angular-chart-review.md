# Independent review of quantitative angular integration

I checked [the principal-chart calculation](angular-principal-chart.md)
and [the mass-dominance calculation](angular-mass-dominance.md), including
the signed use in [the theorem assembly](angular-theorem.md).
I accept the complete angular replacement for $`\log n\ge10^{60}`$
under the two stated mass hypotheses. I also accept the separate
large-radius global bounds for $`\log n\ge10^6`$. The latter still need a
principal-chart estimate at that lower cutoff. My distinct
[phase calibration](angular-phase-calibration.md) is an input here
and outside the scope of this independent review.

## Chart and real Gaussian comparison

The codimension-one torus uses probability Haar measure. In a
chart, fixing coordinate values for the first $`d-1`$ angles determines
the last angle modulo $`2\pi`$, with a real zero-sum lift having
Euclidean Gram determinant $`d`$. Thus the Gaussian mass in these
coordinates is $`(2\pi A)^{-(d-1)/2}/\sqrt d`$ for real precision $`A`$.
The same covolume applies to each odd label. The centered
$`\phi(t)`$ has real part at least $`1-Vt^2/2`$. Using the independent-copy
covariance formula, the Lipschitz factors $`2/d,5/d`$ cost at most
$`2V|t|/d,5V|t|/d`$ before division by $`\phi(t)`$. This gives the
stated bounds for changes in both coefficients. In particular
$`n\Re a(t)`$ is within one percent of $`na`$. The near-chart change
to the real Gaussian mass is at most $`e^{4d|t|}`$. For the principal
labels, $`|\Im a(t)|/\Re a(t)\le3|t|/.99`$ and
$`\log(1+z)\le z`$ give the stated ratio bound $`e^{10dt^2}<2`$ between
the real Gaussian units and the magnitude of the complex Gaussian
units.

The subset expansion is also valid for zero and full row sizes.
Its fourth term is bounded by $`(7/24)a_sQ_4`$, since
$`Q_2^2/d\le Q_4`$. The linear terms in the complex weighted
expectation cancel by definition of the complex coefficients.
For each size function, the shift of its complex weighted mean
is at most twice its real standard deviation. Thus
$`\mathbb E|g_S-g(t)|^2\le5\mathrm{Var}(g_S)`$ by expanding around
the real mean. With the bounds on the two Lipschitz constants this
gives the displayed $`40aQ_2^2/d`$, and the errors for the two terms
$`Q_4`$ and $`Q_2M^3`$ separately fit within the coefficient $`300`$.
The exponential estimate is applied with $`|D_s|+|E_s|<.01`$,
and the subsequent logarithm uses an argument within $`1/2`$ of one.

For the local comparison one factors out $`\phi(t)^n`$ and uses
the real Gaussian of precision $`A=n\Re a(t)`$. Its remaining complex
quadratic factor is a unit-modulus phase. The proof bounds
$`e^H-1`$ in this real Gaussian integral and discards the pure quadratic
tail there. So it bounds a complex difference in absolute value
before conversion to $`|G_t|`$. The underlying Gaussian integral is
analytic in the right half-plane and therefore agrees with the
continued complex power defining $`G_t`$.

The quartic exponential bound uses truncation in each normal
coordinate. The independent average event costs at most two.
The centered-to-independent estimate gives the per-site exponent
$`48000Z_j^4/A`$, which is at most $`.192Z_j^2`$ on the stated
truncation. The resulting product parameter is
$`21\cdot48000d/A=1008000d/A`$. The chi-square formula and
$`-\log(1-x)\le2x`$ give the stated $`Q_2`$ factor. For the maximum
term the cutoff $`M=n^{-2/5}`$ has probability at most
$`2d e^{-A n^{-.8}/2}`$, and integrating its tilted tail costs at most
$`3d e^{-.49A n^{-.8}}`$. The deterministic inequality used there
is $`6000b^3\le.006<.01`$. Hölder with powers three gives the
stated $`2e^{4000dt^2}`$ bound from $`3`$, $`e^{12000dt^2}`$, and $`2`$.

At the principal labels the three norm terms are respectively
controlled by the cubic Wick cancellation, the eighth normal
moment with $`\|Q_4\|_2\le\sqrt{105}d/A^2`$, and
$`\|AQ_2\|_2\le d`$. Multiplying by $`na/A\le1/.99`$ leaves
all three constants within the displayed bounds. The real
Gaussian norm and maximum tails are negligible also at the lower
radius $`10^{-4}`$, because $`A b^2/d\ge10^{-8}u/401`$.
Cauchy–Schwarz and the last exponential bound give the asserted
error in real units, and comparison of the real and complex
normalizations yields the final relative error.

## Global bounds

The capped binomial versus same-mean binomial comparison applies
at every real tilt. The ratio below the cap is a constant times a
geometric progression, and vanishes above it. The sign changes
therefore permit the two-crossing convex-order argument. Since
$`V\le\mu(1-\mu/d)`$, the relation
$`d(d-1)a=\mu(d-\mu)-V`$ implies $`V\le da`$.
The centered moment bound for $`\phi_{\ast}`$, together with
$`|a(t_{\ast})|\le a/|\phi_{\ast}|`$, gives both lower bounds for $`|G_{\ast}|`$.
In particular $`(n+\nu)Vt_{\ast}^2\le15A/d`$ because $`d\le n`$.

The row envelope is applied before taking the $`n`$th power.
In the good-size interval $`w_s\ge a/5`$.
On $`R_0\ge d/2`$ the Bessel and Stirling error is at most
$`(d-R_0)/d+13/(12dw_s)`$, since
$`\tfrac12\log(d/R_0)\le(d-R_0)/d`$.
The first term loses less than a tenth of $`w_s(d-R_0)`$,
and $`D\le2(d-R_0)`$ then gives the stated $`.09aD`$.
On the other part the entire Stirling cost is smaller than the
same fractional loss. Integrating the real mean differential
inequality gives the quoted lower and upper size tails.
Because $`D\le d`$, the bad-size exponent retains the margin
$`.14-.09=.05`$ on factoring out the common pointwise penalty.
The two remaining prefactors are bounded by $`e^{12/(da)}`$.

The transverse balls are disjoint on the torus, since differences
of two candidate lifts lying in an interval of width $`4b<2\pi`$
must be the same real number in every coordinate. Conversely
$`D<b^2/3`$ yields the lift by using principal angles relative to the
argument of the circular mean. Centering those angles can only reduce
the squared norm, and the adjusted common angle has odd label. In the complementary region, the best-anchor
sum of squared chords is $`D+d\min_i|z_i-\bar z|^2\le2D`$.
The worst chord-to-angle factor $`\pi^2/4`$ then gives $`5D`$.
The relative-angle map is onto, and its pushforward measure is
ordinary normalized Haar measure. Splitting the pointwise penalty
and integrating $`d-1`$ full-line real Gaussians gives exactly
$`d^{3/2}(.018)^{-(d-1)/2}`$ in units $`I_0`$, including the
sum over anchors. The displayed losses fit inside the off-ball
penalty at both stated radii and cutoffs.

The adjacent-size estimate uses the conditional mean of the extra
coordinate and its unconditional uniformity. In the remote chart
there is a uniform gap $`10^{-25}`$ even after the error
$`d^{-1/2}`$ from approximating by the response of one fixed size.
At the large cutoff the ball-volume loss and the cost of the
principal normalization fit inside the exponential gap in the
$`n`$th power. For the near labels, the difference of two independent
sizes has an interval log-concave mass and a log-concave survival
sequence. Chebyshev and symmetry give $`T(m)\le1/16`$ and
$`T(0)\ge1/2`$. Taking the looser block ratio $`1/4`$ yields the
stated survival bound and its integrated fourth moment. The cubic
Taylor remainder in $`\sin`$ costs at most
$`(2\cdot10^5/6) V^2t^3<Vt`$ throughout the near range. After
integration the ratio uses $`V(t^2-t_{\ast}^2)/4`$ because it bounds
the logarithm of the modulus, half the logarithm of its square.
The chart factor $`e^{20d|t|}`$ spends at most
$`(\pi^2/20)L(j^2-1)`$ of that exponent. The resulting two-sided
geometric series starts at the first nonprincipal odd label.
No summation factor $`d`$ is needed for this part.

## Larger radius and signed sum

At radius $`2/5`$, the sharp real fourth-order bound yields
$`Q_2/2-1.26Q_4\ge .29Q_2`$. The mean truncation in its Gaussian
expectation can be imposed independently at cost at most $`4/3`$.
The fourth-power inequality follows by convexity using weights
$`8/9,1/9`$. The deterministic shift is at most
$`1.26\cdot9^3\cdot16/(dA_0)<15000/(dA_0)`$.
The random term per coordinate is at most $2A_0 Z_j^4\le
A_0 Z_j^2/3$` under `$|Z_j|\le .401$.
The stated bound by four follows from the elementary normal
moment and $`d/A_0\le800/u`$. For the remote factor,
$`|f_{s_0}|>.97`$ absorbs the additive comparison error.
The precision loss uses $`a_{s_0}\ge a-1/(d-1)`$, since the function
at the mean exceeds its expectation and its Lipschitz constant is
$`1/(d-1)`$. This changes the determinant by at most $`e^{2/a}`$.
For the near factor the size covariance is bounded by the product
of the two Lipschitz constants times $`V`$. The centered Taylor
error in the scalar expectation uses $`B_y\le.08`$ and the
size-function variance bound. Both extra exponents together lose
less than $`.05 nV(t^2-t_{\ast}^2)`$, as is seen by dividing by
$`j^2-1`$ at odd $`j\ge3`$. These estimates independently give the
global-only version at $`u\ge10^6`$.

Finally the signed integral is the integral of $`R^n`$, with
$`H(v)^n>0`$ as the prefactor. Each monomial's exponent vector
survives Haar integration exactly when it is constant, and
the product constraint supplies $`(-1)^k`$ at quota $`k`$.
Negating the angles preserves Haar measure and exchanges the
principal balls, so the complex principal terms are conjugate.
All off-ball and nonprincipal estimates upper bound integrals
of $`|R|^n`$, while the principal error bounds the difference from
the complex Gaussian term. For the complete small-radius argument,
the error summed over all regions is below $`0.23|G_{\ast}|`$ in units of
one principal magnitude. At a geometric node the phase input gives
$`(-1)^k 2\Re G_{\ast}>1.9|G_{\ast}|`$, and the total integral has the
strict required sign. The same error reasoning applies at a node
with exact phase $`k\pi`$.
