# Independent review of the principal charts at the original cutoff

I accept the principal estimate $`|I_t-G_t|<.02|G_t|`$ for the ball of radius $`2/5`$ at $`t=\pm\pi/d`$, $`u=\log n\ge10^6`$, $`n^{.99}\le d\le n`$, and $`A/d\ge u/111`$. The hypotheses match the larger-radius global argument once the variance bound from the geometric-tilt transfer is included. In that setting the combined error from the two principal charts and the three remaining regions is less than $`.07|G_t|`$. [Principal chart calculation](angular-principal-lower.md) · [Larger-radius global calculation](angular-mass-dominance.md#larger-radius-global-version-at-the-original-row-cutoff)

## Hypotheses and Gaussian normalization

At the quota center tilt $`w`$, the overlap gives $`nV_w/d^2>u/110`$. The phase calibration gives $`|\log(v/w)|<3/d`$ at the geometric tilt $`v`$. Along the intervening real tilts, the likelihood ratios are between $`e^{-3}`$ and $`e^3`$, so the standard deviation stays above $`e^{-3/2}n^{.49}>10^4`$. The log-variance derivative satisfies $`|(\log V)'|\le10^9\sqrt V\le10^9\sqrt d/2`$ there. Consequently $`|\log(V_v/V_w)|\le1.5\cdot10^9/\sqrt d<\log(111/110)`$. This gives $`nV_v/d^2>u/111`$ and, because $`V_v\le d a_v`$, $`A/d=na_v/d>u/111`$. The same transfer establishes both global hypotheses $`A/d,nV_v/d^2\ge u/400`$. It supplies the stronger precision through $`V_v\le da_v`$ even though the separate bound from $`x_v(1-x_v)`$ is only $`u/201`$. [Variance transfer](angular-phase-review.md#transfer-to-the-geometric-tilt)

Set $`a=\mathbb E a_S`$, $`\nu=(d-1)/2`$, and $`A_t=n\Re a(t)`$. The variance bound gives $`Vt^2\le10a/d`$ at the two principal angles, so they lie in the global near band $`|t|\sqrt V\le10^{-3}`$. In particular $`|\phi(t)|>.999`$. The covariance bound comes from independent pairs, and for complex $`c`$ the identity $`\mathbb E|g-c|^2=\mathrm{Var}(g)+|\mathbb E g-c|^2`$ gives the second-moment bound in the principal note. The exact derivatives of $`a_s`$ and $`\gamma_s`$ are bounded in absolute value by $`1/(d-1)`$ and $`d/((d-1)(d-2))`$, respectively. For the latter use $`|d^2-6ds+6s^2|\le d^2`$ for $`0\le s\le d`$. These imply the claimed bounds $`|a(t)-a|\le3a|t|`$, $`|\gamma(t)|\le1.01a`$, and $`|\Im\gamma(t)|\le3.01a|t|`$. Thus $`A_t\ge.999A`$ and $`A_t/d\ge u/112`$.

In the Euclidean measure on the sum-zero subspace the Haar density of a chart is $`(2\pi)^{-(d-1)}/\sqrt d`$, since the map recovering the last angle from the first $`d-1`$ has Gram determinant $`d`$. The complex Gaussian is convergent since $`A_t>0`$. The ratio of real and complex normalization magnitudes obeys $`\log(J_t/|G_t|)\le(d/4)(3/.999)^2 t^2<3dt^2`$, so $`J_t<1.001|G_t|`$. This matches the Gaussian and branch convention in the global note.

## Inner chart and fourth powers

Let $`\varepsilon=n^{-2/5}`$ and restrict first to $`M=\max_j|y_j|\le\varepsilon`$. The fixed-size logarithm has quadratic and cubic terms $`L_s=-a_sQ_2/2-i\gamma_s Q_3/6`$ and an error bounded by $`a_s((7/24)Q_4+8Q_2M^3)`$. The coefficient $`7/24`$ is $`1/24+(2/8)`$ after $`Q_2^2/d\le Q_4`$. For $`D_s=L_s-\mathbb E_t L_S`$, the two variance bounds and $`|Q_3|\le M Q_2`$ give

$$
\Vert D_S\Vert _2
\le \left(\frac{1.01}{2}+\frac{3.01}{6}M\right)Q_2\frac{\sqrt V}{d}
<.52\thinspace{}Q_2\frac{\sqrt V}{d}.
$$

Use $`V\le da`$ again to get $`\mathbb E|D_S|^2<.28aQ_4`$. The uniform bound $`|D_s|+|E_s|<.06`$ follows from $`a_s\le.26`$, $`Q_2\le.16`$ and $`M<.001`$. Splitting $`e^{D_s+E_s}-1-D_s`$ at $`e^{D_s}`$ gives coefficients at most $`e^{.06}<1.1`$ and $`e^{.06}/2<.55`$ for $`|E_s|`$ and $`|D_s|^2`$. Thus averaging with the complex weights costs at most $`1/.999`$, and the linear $`D_S`$ contribution vanishes. The coefficient of $`aQ_4`$ is at most $`(1.1(7/24)+.55(.28))/.999<.5`$. The coefficient of $`aQ_2M^3`$ is less than nine. The resulting quantity is below $`.01`$, making the logarithm loss at most $`1/.99`$. This yields $`.52aQ_4+10aQ_2M^3`$ as stated. [Exact fixed-size expansion](direct-row-expansion.md)

For the large-ball estimate, let $`Y_j=Z_j-\bar Z`$ with independent $`Z_j`$ of variance $`1/B`$, $`B\ge A/2`$. Restrict the independent mean to $`|\bar Z|\le2/\sqrt{dB}`$ at probability at least $`3/4`$. On the ball, the resulting $`|Z_j|`$ is at most $`.401`$. Weighted convexity gives $`|Y_j|^4\le(9/8)^3|Z_j|^4+9^3|\bar Z|^4`$. At coefficient $`1.68 B`$, the shift costs at most $`1.68\cdot729\cdot16/(dB)<.01`$. Per coordinate $`1.68(9/8)^3<2.4`$ and $`2.4(.401)^2<.4`$. For a standard normal $`X`$ the moment $`\mathbb E[X^4e^{.4X^2}]=3\cdot5^{5/2}<170`$, by differentiating the Gaussian squared moment generating function. The product bound is therefore

$$
\frac43\exp(.01+408d/B)<4
$$

using $`d/B\le222/u`$. This also proves the weaker $`1.26`$-coefficient exponential moment needed by the global argument.

With $`H=-in\gamma(t)Q_3/6+nE`$, Wick cancellation on the zero-sum Gaussian gives $`\|Q_3\|_2\le\sqrt{6d}/A_t^{3/2}`$. The marginal eighth moments and the radial chi-square moment give $`\|Q_4\|_2\le\sqrt{105}d/A_t^2`$ and $`\|A_tQ_2\|_2\le d`$. Replacing $`A/A_t`$ by $`1/.999`$ gives the coefficients $`.42`$, $`5.4`$, $`11`$ in the bound for $`\|\mathbf1_{\mathcal I}H\|_2`$. Substitution of $`d/A_t\le112/u`$ gives less than $`.006`$. The positive real cubic plus the $`10A Q_2M^3`$ part costs less than $`.001`$ because $`A|t|\le4n^{.01}`$ and $`M\le\varepsilon`$. Hence $`(\Re H)_+\le .53A_tQ_4+.001`$, and the fourth-power estimate gives $`\mathbb E[\mathbf1_{\mathcal I}e^{2(\Re H)_+}]<5`$. The error on the inner region is at most $`.006\sqrt5\,J_t<.014J_t`$.

## Tail comparison and global compatibility

For the complex Gaussian tail it suffices to take the absolute integral at precision $`A_t`$. The maximum bound is $`2d e^{-A_t\varepsilon^2/2}`$, and the chi-square bound outside $`Q_2\le(2/5)^2`$ is $`2^{(d-1)/2}e^{-.04A_t}<e^{-300d}`$. Both are below the stated $`.001J_t`$ allowance after addition.

The real part of the fixed-size logarithm on the large ball is bounded by $`-a_sB_y`$, $`B_y=Q_2/2-1.26Q_4`$. Here the quartic and real remainder together cost at most $`(7/24+6(2/5)^2)a_sQ_4<1.26a_sQ_4`$. Also $`B_y\ge(.5-1.26(2/5)^2)Q_2>.29Q_2`$. For mixed sizes, the adjacent-size coupling gives $`|f_{s+1}-f_s|\le3Q_2/(2d)`$. To check it, use a uniform added element $`J`$ and expand $`e^{iy_J}-1`$. The conditional mean is $`-L_s/(d-s)`$, so the centered linear contribution costs at most $`\mathbb E L_s^2/(d-s)\le Q_2/d`$. The remainder costs $`Q_2/(2d)`$ since $`J`$ is uniformly distributed before conditioning. The independent-pair identity and $`\mathrm{Var}(a_S)\le V/(d-1)^2`$ now give the matching near envelope

$$
|R(t,y)|^n\le|\phi(t)|^n
 \exp\left[-A Q_2/2+1.26 A Q_4+
 \frac{nVB_y^2}{(d-1)^2}+\frac{2nVQ_2|t|}{d}\right].
$$

At the principal angle, the last two terms cost less than $`2 nV/d^2\le2A/d`$, using $`B_y\le.08`$ and $`Q_2\le.16`$. The Hölder exponents $`4/3`$ and $`4`$ produce the correct coefficient $`1.68`$ and the fourth root of the maximum tail. After conversion to principal units the ratio is at most $`4e^2(2d)^{1/4}\exp(2A/d-A\varepsilon^2/8)`$. Since $`d\varepsilon^2\ge n^{.19}>32`$, at least $`A\varepsilon^2/16\ge u n^{.19}/1776>100u`$ remains in the negative exponent. This is well below $`.001`$ after all prefactors. Summing with the other errors gives at most $`.015 J_t+.001|G_t|<.02|G_t|`$.

The same large balls are disjoint, and the off-ball comparison has logarithmic ratio at most $`12n/(da)-.0024A+3d+15A/d<-.001A`$, already under the weaker global precision $`A/d\ge u/400`$. For remote labels the scalar modulus gap and the adjacent-size coupling factor as $`|R|\le e^{-10^{-25}}|f_{\lfloor\mu\rfloor}|`$, since $`|f_{\lfloor\mu\rfloor}|>.97`$ and the additive cost is at most $`d^{-1/2}`$. The row-specific precision survives as $`n a_{\lfloor\mu\rfloor}\ge A/2`$, with determinant ratio at most $`e^{2/a}`$ since $`a_{\lfloor\mu\rfloor}\ge a-1/(d-1)`$. This gives the stated $`4d\exp(-10^{-25}n+2/a+15A/d)`$ remote bound below $`1/100`$.

For all nonprincipal near labels $`|t|=j t_{\ast}`$, odd $`j\ge3`$, the last two terms in the envelope are at most $`nV(.01/d^2+.32|t|/d)<.05nV(t^2-t_{\ast}^2)`$, since $`j/(j^2-1)\le3/8`$. The fourth moment bound for the symmetrized row-size law gives the radial penalty at least $`nV(t^2-t_{\ast}^2)/4`$. Together with the quartic Gaussian bound this leaves the same convergent series as in the global note, with $`nV/d^2\ge u/400\ge2500`$. The three global contributions therefore cost less than $`.03|G_t|`$, as required for the strict combined $`.07`$ bound.

At a low-curvature geometric node, the prior calibrated phase makes the signed sum of the two conjugate leading terms greater than $`1.9|G_t|`$. The remainder above is smaller. This checks the angular step at the original cutoff under the stated variance transfer and overlap hypotheses. It is a statement for the specified dimension and height regime.
