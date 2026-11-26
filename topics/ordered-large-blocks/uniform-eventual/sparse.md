# Moving outer ranks in the sparse saddle regime

Let $`O_{n,j}`$ mark blocks of size at least $`j`$ in all ordered partitions of $`[n]`$. Write $`n=jm+s`$, $`0\le s<j`$, and let $`h`$ be a zero-based rank in decreasing original modulus. Suppose

$$
h\to\infty,\qquad h/j\to0,\qquad h^2/m\to0.
 \tag{1}
$$

The old and new roots at this rank and neighboring ranks are simple and negative, with these ranks counted among all complex roots. Write $`a_h,b_h`$ for the old and new original moduli. At equal degrees $`a_h>b_h>a_{h+1}`$. At the carry $`b_h>a_h>b_{h+1}`$. The conditions in (1) are precisely $`j/\sigma_h\to\infty`$ in this moving-rank setting, where $`\sigma_h`$ is the coefficient saddle standard deviation. The argument allows arbitrary relative growth of $`j,m`$. [Independent review](review-sparse.md)

The inputs are the published reciprocal ordered-block generating function and the positive coefficient and fixed-rank carry estimates in the two reviewed [outer-rank arguments](../outer-ranks/README.md). Use the notation of their renewal proof. Let $`\rho_j`$ be the positive root of $`S_j(\rho_j)=1`$ and set

$$
T(z)=(1-S_j(\rho_j z))^{-1},\qquad
 U(z)=\sum_{a\ge0}\frac{j!(\rho_j z)^a}{(j+a)!},\qquad
 F_p=T^{p+1}U^p,\quad C_p(e)=[z^e]F_p(z).
$$

The old reversed coefficients before common positive rescaling are

$$
d_t=(j!)^{-(m-t)}\rho_j^{-(s+jt)} C_{m-t}(s+jt).
$$

Use $`p_t=m-t`$, $`e_t=s+jt`$. The reciprocal variable of this reversed row is denoted by $`y`$; a zero $`-y`$ with $`y>0`$ corresponds to original modulus $`1/y`$.

## Tilt estimates with a signed difference

For a series with nonnegative coefficients and radius of convergence at least 1, tilt at $`r\in(0,1)`$ by taking the probability of degree $`e`$ proportional to its coefficient times $`r^e`$. Denote the point mass of the tilted $`F_p`$ by $`P_{p,r}(e)`$, its mean by $`\mu_p(r)`$, and its variance by $`\sigma_p(r)^2`$. Let $`w=r/(1-r)`$. Uniformly in sufficiently large $`j`$, all $`p\ge1`$, and $`r\in(0,1)`$,

$$
\mu_p(r)\asymp p w,\qquad \sigma_p(r)^2\asymp p w(1+w).
 \tag{2}
$$

For $`p=0`$ replace $`p`$ by 1. Near the pole use $`T(z)=A(z)/(1-z)`$ with bounded analytic $`A`$ and logarithmic derivatives in a fixed neighborhood of the closed unit disk, as in the renewal proof. Its geometric factor supplies the mean $`w`$ and variance $`w(1+w)`$; analytic contributions are bounded. On each compact radius interval below 1 the moments of each factor are $`O(r)`$, and probabilities of degrees zero and one in $`T`$ are bounded below by $`c`$ and $`cr`$.

The following point-mass estimates hold along $`p\to\infty`$ with $`pw\to\infty`$, at an integer mean $`e=\mu_p(r)`$:

$$
P_{p,r}(e)\asymp 1/\sigma_p(r),\qquad
 |P_{p,r}(e+1)-P_{p,r}(e)|
   \le C(1+w)/\sigma_p(r)^3 .
 \tag{3}
$$

The supremum of all point masses is at most $`C/\sigma_p(r)`$ in this regime. For any $`p\ge0`$, including nonlarge $`p`$, the single factor $`T`$ gives the separate bound $`C/(1+w)`$ on the point masses: its coefficients are uniformly bounded and $`T(r)\asymp1+w`$, and convolution cannot increase the maximal mass.

Here are details that preserve the scale in (3) when $`w`$ is arbitrarily large. Away from the pole the zero and one masses of $`T`$ give $`|\phi_T(\theta)|\le \exp(-cr\theta^2)`$ for $`|\theta|\le\pi`$. Near the pole, the ratio of the absolute values of the analytic factors is at most $`\exp(C\theta^2)`$. Its logarithm has zero linear term because the coefficients are real and the real-axis logarithmic derivative is real. The geometric factor gives modulus $`(1+4w(1+w)\sin^2(\theta/2))^{-1/2}`$. If $`w`$ is sufficiently large, half its logarithmic decay absorbs $`C\theta^2`$ uniformly on $`[-\pi,\pi]`$, since $`\log(1+c w^2\theta^2)/\theta^2`$ decreases with $`|\theta|`$ and its value at $`\pi`$ tends to infinity. Thus $`|\phi_T(\theta)|\le (1+c w^2\theta^2)^{-1/4}`$ there. The $`U`$ factors have modulus at most one. Integrating the resulting product bounds gives the point-mass supremum estimate.

Write $`\varphi`$ for the centered characteristic function of $`F_p`$. On $`|\theta|\le c_0/(1+w)`$, its logarithm equals

$$
-\sigma^2\theta^2/2+O(pw(1+w)^2|\theta|^3).
$$

The third derivative bound follows by differentiating the geometric logarithm and the bounded analytic logarithms; their compact-radius bounds are $`O(r)`$ when $`r\to0`$. Choose $`c_0`$ small enough that the error costs at most a fixed fraction of the Gaussian decay. Interpolation between the exponentials bounds the difference from the Gaussian by $`Cpw(1+w)^2|\theta|^3 e^{-c\sigma^2\theta^2}`$. Thus Fourier inversion gives the first estimate of (3), since $`(1+w)/\sigma=o(1)`$. For the difference insert the factor $`e^{-i\theta}-1`$. Its linear term integrates to zero on the symmetric Gaussian interval; the quadratic term costs $`O(\sigma^{-3})`$ and the product with the characteristic-function error costs $`O(pw(1+w)^2/\sigma^5)`$. On the remaining arc, the compact-radius Gaussian bound is exponentially small in $`pw`$. Near the pole change variables $`v=(1+w)\theta`$; integrating with the factor $`|\theta|`$ bounds that tail by $`C(1+w)^{-2}e^{-cp}`$. These are bounded by the claimed signed error. In particular, letting $`r_t`$ satisfy $`\mu_{p_t}(r_t)=e_t`$, for $`t`$ comparable to $`h`$ we have

$$
\log \frac{C_{p_t}(e_t+1)}{C_{p_t}(e_t)}
    =-\log r_t+O(1/e_t).
 \tag{4}
$$


Write $`\sigma_h=\sigma_{p_h}(r_h)`$, $`K=j^2/\sigma_h^2`$ and $`\Delta=j/\sigma_h^2`$. Formula (2) gives

$$
K^{-1}\asymp h/j+h^2/m,\qquad
 \Delta\asymp \frac1{h(1+jh/m)}.
$$

For $`h/2\le t\le 2h`$, the saddle values $`w_t`$ and variances are comparable to their values at $`h`$. Between consecutive saddles the difference in mean for the same law is $`j+O(w_h)\sim j`$: decreasing $`p`$ by one removes one $`T`$ and one $`U`$ factor. Integrating the variance with respect to log-radius gives $`\log(r_{t+1}/r_t)\asymp\Delta`$ throughout this range. In particular it is positive and $`1/e_h=o(\Delta)`$ by (1).

## Two-term localization with all coefficients included

Let $`y_h=d_h/d_{h+1}`$ and $`D(r)=j!\rho_j^{-j}r^{-j}/(T(r)U(r))`$. At any fixed tilt $`r`$ the ratios of reversed coefficients obey

$$
d_t/d_v=D(r)^{t-v}P_{p_t,r}(e_t)/P_{p_v,r}(e_v).
 \tag{5}
$$

At $`r_{h+1}`$ the old law $`p_h`$ is displaced from its mean by $`\asymp j`$; at $`r_h`$ the other law is displaced by the same amount. Moving each law back to its own saddle gives the exact change-of-tilt factor
$`\exp(\log F_p(r)-\log F_p(\tilde r)-e\log(r/\tilde r))`$ when converting a point mass at $`r`$ to its value at $`\tilde r`$. Equivalently the off-mean point mass equals the at-mean one times the exponential of the negative tangent discrepancy of $`\log F_p`$ in log-radius. The variance comparison between the two tilts gives discrepancy $`\ge c j^2/\sigma_h^2`$. Crucially, the at-mean bound in (3) supplies the same $`1/\sigma_h`$ at the displaced point as at the corresponding neighboring saddle. Therefore

$$
y_h D(r_{h+1})\le C e^{-cK},\qquad (y_h D(r_h))^{-1}\le C e^{-cK}.
$$

Use the first tilt for $`t\ge h+2`$ and the second for $`t\le h-1`$ in (5), always dividing by the central term at that tilt. If $`p_t\ge m/2`$ the supremum of point masses at the fixed tilt has size $`O(1/\sigma_h)`$ by (3)'s supremum argument. For $`p_t<m/2`$ the single-factor bound $`C/(1+w_h)`$ loses at most $`O(\sqrt m)`$ after division by a central mass. This latter range is at distance $`\asymp m`$ and its polynomial loss is absorbed by the geometric ratio. As a result, throughout $`1/2\le |z|\le2`$, the normalized off-central tail at $`y=y_h z`$, after division by $`d_h(y_hz)^h`$, tends to zero exponentially in $`K`$. The bound per index is $`Ce^{-cK l}`$, with $`l`$ the distance to the central pair, except for the absorbable distant loss just described. The normalized central pair is $`1+z`$.

Rouché on $`|z|=1/2,2`$ gives respectively $`h`$ and $`h+1`$ roots inside the contours with multiplicity, by comparison with the corresponding dominant monomials. On a small disk about $`-1`$ inside the annulus it gives exactly one root, which is real by conjugacy and simple. It is negative and has modulus $`y_h(1+o(1))`$. This is rank $`h`$ under the zero-based original-modulus convention. Applying the same reasoning to $`h\pm1`$ gives exponentially separated neighboring balances: use the first right-tail term at $`h`$ to obtain $`y_h/y_{h+1}\le Ce^{-cK}`$.

## Consecutive sign with the exceptional leading coefficient

Put $`\gamma_t=C_{p_t}(e_t+1)/C_{p_t}(e_t)`$. The same-degree next coefficients, up to their common positive factor, are $`d_t\gamma_t`$. From (4),

$$
\gamma_h-\gamma_{h+1}\asymp \gamma_h\Delta\asymp m/(jh^2)>0.
$$

Indeed $`\gamma_h\asymp(1+w_h)/w_h`$, $`w_h\asymp jh/m`$, and the error $`O(1/e_h)`$ in the logarithm is $`o(\Delta)`$. For indices in $`[h/2,2h]`$, summing consecutive log-radius gaps and using (4) gives $`|\gamma_t-\gamma_{h+1}|\le C(|t-h|+1)\gamma_h\Delta`$. The exponential tails therefore dominate the cost of these signed differences relative to $`\gamma_h\Delta`$.

For other $`t\ge1`$, use the renewal estimate $`0\le\gamma_t-1\le C p_t/(e_t+1)`$ for $`p_t\ge1`$, and its exponentially small $`p_t=0`$ replacement. This bounds the signed cost relative to $`\gamma_h\Delta`$ by $`C(h+h^2/t)`$. Since these terms are at distance at least a positive multiple of $`h`$, the geometric tails absorb the cost, including the $`O(\sqrt m)`$ prefactor when $`p_t<m/2`$.

The exceptional index $`t=0`$ has signed relative cost at most $`Cjh^2/(s+1)+Ch`$. If $`j\le m`$, the distance-$`h`$ bound suffices: $`hK\asymp \min(j,m/h)`$, which grows faster than $`\log(jh^2)`$ because $`h=o(j)`$, $`h^2=o(m)`$, and $`j\le m`$. If $`j>m`$, use the coefficient comparison (1) in the renewal proof directly. At the anchor indices $`h,h+1`$, replace the respective binomial coefficients by their leading powers with log error $`O(1+m^2/(jh))`$. At index zero use $`\binom{s+m}{m}\le (s+m)^m/m!`$ and log error $`O(m)`$. In the ratio $`d_0d_{h+1}^h/d_h^{h+1}`$ the linear normalizations cancel and the total log error is $`O(m+h+m^2/j)=O(m)`$. With $`u=s/j`$, the power factors satisfy

$$
\frac{(u+h+1)^{h(m-h-1)}}{(u+h)^{(h+1)(m-h)}}\le
 (u+h)^{-m}e^m,
$$

and the factorial ratio $`(m-h)!^{h+1}/(m!(m-h-1)!^h)`$ is at most one. Thus $`d_0d_{h+1}^h/d_h^{h+1}\le(C(s+m)/(jh))^m`$. The bound absorbs $`2^h`$ and the signed cost, since $`x=(s+m)/(jh)\to0`$ and $`jh^2/(s+1)\le mh/x`$. This treatment has no upper limit on $`j`$.

At the actual old root subtract $`\gamma_{h+1}`$ times the old reversed row, which vanishes there. The surviving central term has sign $`(-1)^h`$ and absolute size $`(\gamma_h-\gamma_{h+1})d_h |y|^h`$. All other terms are little-oh of this size by the signed estimates. Both old and new balances at the matching rank differ by a factor tending to one, from (4); the neighboring balances are exponentially separated. For the next row, the disk count before the matching annulus has parity equal to the number of its negative real roots there, since nonreal roots are conjugate pairs and positive-axis values are positive. The strict sign therefore places the old reciprocal root before the matching next reciprocal root and after the preceding one. Applying the same comparison at $`h+1`$, or using its separated balance, gives the fixed-degree order claimed above.

## Carry

At $`s=j-1`$, the next reversed row is $`d^*+\rho_j^{-1} y\sum_t d_t\gamma_t y^t`$, $`d^*=(j!)^{-(m+1)}`$. On old rank $`h`$, the comparison's signed scale after stripping the factor $`y/\rho_j`$ is $`\asymp m/(jh^2)\,d_h|y|^h`$. We have $`|y|>y_0`$ eventually: the rank-$`h`$ Rouché count puts the fixed smallest reciprocal root inside $`y_h/2`$, the fixed-rank theorem places it at $`y_0(1+o(1))`$, and the moving root is at $`y_h(1+o(1))`$. The unweighted off-central estimate at the moving root gives $`d_0=o(d_h|y|^h)`$. Consequently it suffices that $`\rho_j d^*/(y_0d_0)=o(m/(jh^2))`$.

If $`j/m\to\infty`$, the renewal carry calculation bounds this last ratio by $`(m/j)(C m/j)^m`$, which suffices. On any subsequence with $`j/m\le C`$, use the reviewed comparable-threshold first two balances: the extra new balance is exponentially smaller in $`j`$ than the following new balance, which is $`O(j)`$ times the old first balance. The ratio $`\rho_j d^*/(y_0 d_0)`$ is $`\gamma_0`$ times the extra new balance divided by $`y_0`$. Since $`\gamma_0=O(1+m/j)`$, this is again $`o(m/(jh^2))`$. These cases exhaust arbitrary growth by subsequences.

The carry constant therefore preserves the strict signed comparison, with the sign reversed by the extra negative reciprocal factor. The matching next rank is $`h+1`$, since its two central coefficients are the old ones shifted by one and altered by $`\gamma_h,\gamma_{h+1}`$. The moving-rank Rouché argument applies also there with the new degree and residue, and the preceding new rank is exponentially closer to zero. The old reciprocal root lies strictly between the next roots at ranks $`h`$ and $`h+1`$. Inverting yields the asserted carry bracket.
