# Explicit geometric-node tolerances at any positive linear aspect

The theta comparison is already part of the
[effective high-cap sector](../effective-sectors/sector-proof.md).
Its [logarithmic sector supplement](../effective-sectors/sector-logarithmic.md)
also uses Poisson summation for the lower bound. The new quantitative
ingredient here is a tolerance in terms of the *actual center curvature*,
with Gaussian-weighted perturbation control instead of treating every
term in the finite window at its maximum relative error. This gives an
explicit all-cap reduction. The estimate for the change in the balancing probability is proved separately.

## A finite sign lemma

Let $`P(z)=\sum_{j=0}^D a_jz^j`$ have positive log-concave coefficients and
put $`b_j=\log(a_j^2/(a_{j-1}a_{j+1}))`$ at its internal indices. For a
center $`k`$ define $`t_k=\sqrt{a_{k-1}/a_{k+1}}`$. If $`b_k>\log4`$,
coefficient separation gives $`(-1)^kP(-t_k)>0`$. Otherwise suppose
$`0<\lambda\le b_k/2\le\log2`$. Let $`J`$ be the smallest odd integer
at least $`2/\lambda`$ and set

$$
\epsilon_{\theta}(\lambda)=\frac{\lambda}{4}
  \exp\left(-\frac{\pi^2}{4\lambda}\right).
$$

If $`k-J\ge0`$, $`k+J\le D`$, and
$`|b_{k+i}-b_k|\le\epsilon_{\theta}(\lambda)`$ for $`1\le |i|\le J-1`$,
then $`(-1)^kP(-t_k)>0`$. The radius is explicitly smaller than
$`2/\lambda+2`$.

To prove this, write $`w_{\pm j}=a_{k\pm j}t_k^{\pm j}/a_k`$ and
$`a=b_k/2`$. The normalized first neighbors are both $`e^{-a}`$.
Iterating the logarithmic coefficient ratios on each side gives

$$
\log w_{\pm j}=-j b_k/2-\sum_{i=1}^{j-1}(j-i)b_{k\pm i}.
$$

Let $`\epsilon=\epsilon_\theta(\lambda)`$. At $`j\le J`$, the exponent differs
from $`-a j^2`$ by at most $`\epsilon j^2/2`$. The difference of exponentials
is therefore at most $`(\epsilon j^2/2)e^{-\lambda j^2/2}`$, using
$`a\ge\lambda`$ and $`\epsilon\le\lambda`$. Summing both sides of the
center bounds the perturbation by

$$
\epsilon\sum_{j\ge1}j^2e^{-\lambda j^2/2}
\le 3\epsilon\lambda^{-3/2}.
$$

Indeed $`j^2e^{-\lambda j^2/4}\le4/(e\lambda)`$, and the remaining
Gaussian sum is at most its integral on $`[0,\infty)`$, which equals
$`\sqrt{\pi/\lambda}`$. We used $`4\sqrt\pi/e<3`$.

Poisson summation at frequency one half gives

$$
\sum_{j\in\mathbb Z}(-1)^j e^{-a j^2}
=\sqrt{\pi/a}\sum_{m\in\mathbb Z}e^{-\pi^2(m+1/2)^2/a}
\ge 2\sqrt{\pi/\lambda}e^{-\pi^2/(4\lambda)}=:M_\lambda .
$$

For the last step keep just $`m=0,-1`$ and note that
$`a^{-1/2}e^{-\pi^2/(4a)}`$ increases up to $`a=\pi^2/2`$.
The perturbation above is less than $`M_\lambda/4`$.
The omitted ideal tail has absolute value at most
$`2e^{-\lambda(J+1)^2}/(1-e^{-\lambda(2J+3)})`$.
Since $`J\ge2/\lambda`$, $`\pi^2<10`$, and $`\lambda\le\log2<.7`$,
its ratio to $`M_\lambda`$ is at most
$`e^{-3/(2\lambda)}/(1-e^{-4})<7/48<1/6`$.
Thus the truncated actual signed sum is strictly positive. The
remaining actual terms start at even distance from the center because
$`J`$ is odd. Their magnitudes decrease outward by log-concavity, so
pairing them leaves a nonnegative contribution on each side.

For the baseline $`b_j\ge4\delta/(1+2/n)`$ at prescribed $`\delta>0`$,
one can use $`\lambda=2\delta/(1+2/n)`$ whenever there are difficult
centers. Alternatively fix any positive $`\lambda<2\delta`$ with
$`\lambda\le\log2`$ and require $`n`$ large enough that the baseline implies
it. The tolerance has exponential order $`\exp(-\pi^2/(8\delta))`$ as
$`\lambda`$ approaches $`2\delta`$, rather than the $`\exp(-O(\delta^{-2}))`$
lower bound from the crude triple-product estimate. No claim of
optimality or novelty for the underlying sign method is made.

## From the profile comparison to scalar curvature

Take $`0<\delta\le1`$, $`\delta n\le d\le n`$ and $`1\le r\le d`$.
The orientation baseline implies that every difficult center
$`\Gamma_k\le4`$ has $`k/n\in(\delta/4,1-\delta/4)`$ for $`n\ge8/\delta`$.
For example, when $`x=k/n\le\delta/4`$, the baseline logarithm is at
least $`d/(k+1)\ge8/3>\log4`$, using $`\log(1+u)\ge u/(1+u)`$.
The opposite side is symmetric. Larger dimensions $`d\ge n`$ are
already covered by separation.

Suppose that an effective balancing comparison gives
$`|E_{j+1}-E_j|\le\epsilon_\theta(\lambda)/16`$ for consecutive feasible
quotas with densities in $`[\delta/8,1-\delta/8]`$, for all sufficiently
large $`n`$. Here $`E_j=\log(Q_j/L_j)`$ is as in [scalar.md](../adjacent-quotas/scalar.md);
a constant factor such as $`\sqrt d`$ in the normalization cancels.
Only the two immediately adjacent edges and the edges in the feasible local window are used. The proof applies when the slope estimate is available at these edges. The following deductions reduce all difficult centers to the sign lemma.

First apply the comparison only at the two immediate edges of a
difficult center, which are feasible even next to saturation. The
contribution of the baseline $`\log L`$ is $`O_\delta(1/n)`$ by a second
derivative bound on this density window. Thus the logarithmic scalar
deficit curvature is less than two when $`n`$ is sufficiently large.
The [scalar deficit comparison](../adjacent-quotas/README.md)
bounds it below by

$$
\frac{d(n-1)}{n+d(h+1)-1}\log(1+1/h)
\ge \frac{n-1}{(h+1)(h+1+1/\delta)},
\qquad h=nr/d-k.
$$

This forces $`h>\sqrt n/2`$ for large $`n`$: if $`h\le\sqrt n/2`$ and
$`n\ge100(1+1/\delta)^2`$, the denominator is at most $`(.6\sqrt n)^2`$.
Thus the full fixed window of radius $`J+1`$ is feasible at every
difficult center. There is no need to assume a separate saturation strip.

Second, the proof of [scalar.md](../adjacent-quotas/scalar.md) applies uniformly on this
fixed window. For clarity, for $`n`$ sufficiently large each local
deficit is at least $`\sqrt n/4`$ and each density at least $`\delta/8`$,
so the carried-load bound gives $`V\ge\delta^2\sqrt n/32`$ at the tilted
row means. The explicit scalar local limit estimate then applies.
The scalar prefactor curvature is $`O(10^9\delta^{-1}n^{-1/4})`$ by
the standard-deviation Lipschitz bound. Its local-limit log error is
$`O(10^{11}n^{-1/4})`$. These bounds follow directly from the constants
in scalar.md and are effective. The center entropy curvature is
therefore at most three for large $`n`$. Its triangular-kernel
representation then gives $`\sigma\ge\delta\sqrt{n/3}`$ at some
center-window mean. Using $`|d\sigma/d\mu|\le10^9`$ over at most $`J+2`$
mean units ensures $`\sigma\ge\delta\sqrt n/2`$ on the whole window
for explicitly large $`n`$. The variation in rate curvature between
the center and any of its tested indices is at most
$`16\cdot10^9J\delta^{-3}/\sqrt n`$, since
$`|(1/V)'|\le2\cdot10^9/\sigma^3`$. The profile error contributes
at most four times its assumed slope tolerance to the variation.
The scalar errors and the baseline density curvature can each be
made smaller than the remaining margin by increasing $`n`$ by a
computable amount. Hence the required log-curvature tolerance holds.
The sign lemma and increasing geometric nodes give all simple
negative roots.

For example, an explicit sufficient row cutoff *in addition to that
required by the hypothesized profile comparison* is any integer satisfying

$$
n\ge10^{200},\qquad
\sqrt n\ge\frac{10^{12}(J+2)}{\delta^3\epsilon_\theta(\lambda)},\qquad
n^{1/4}\ge\frac{10^{14}}{\delta\epsilon_\theta(\lambda)},
\qquad
\lambda\le\frac{2\delta}{1+2/n}.
$$

Here $`0<\lambda\le\log2`$ can be fixed strictly below $`2\delta`$.
The inequalities ensure that the window fits in the feasible support
and density interval after the deficit bootstrap. They make the
scalar prefactor and local-limit log errors together smaller than
$`\epsilon_\theta/16`$, since those errors are bounded in each
curvature by $`(5\cdot10^{11}/\delta)n^{-1/4}`$.
The absolute baseline density-curvature error is at most
$`64/(\delta^2 n)<\epsilon_\theta/16`$. The standard-deviation bootstrap
loses at most $`10^9(J+2)`$, and the entropy variation bound above is
smaller than $`\epsilon_\theta/16`$. Taking differences of the two
curvatures and adding the assumed slope losses therefore stays
strictly below $`\epsilon_\theta`$. These constants are intentionally loose.

The [direct quota comparison](direct-comparison.md) gives the slopes on every necessary edge for the [explicit logarithmic dimension bound](README.md).
