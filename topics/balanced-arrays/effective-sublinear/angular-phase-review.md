# Independent review of the phase at geometric nodes

The neighboring-quota comparison extends to $`n^{.99}\le d\le n`$ with the stated $`n^{-1/8}`$ error. The resulting displacement has the sign and accuracy needed for the order-one phase cancellation. The row-size and transverse variances at the geometric tilt retain the two logarithmic lower bounds. I give an explicit transfer below, including the variance of the row law weighted by the transverse coefficient. These inputs control the principal Gaussian pair and suppress the other leading Gaussian terms in a near angular band. Chart integration errors and the remaining angular regions require separate estimates. [Overlap reduction](angular-overlap.md) · [Phase calibration](angular-phase-calibration.md)

## Neighbor comparison and overlap

Write $`u=\log n\ge10^6`$, $`s=d/n`$, $`\eta=n^{-1/4}`$, and $`T=100/\min(s,1/4)\le400e^{.01u}`$. All inequalities below concern consecutive feasible quotas with both densities in $`[s/3,1-s/3]`$, including a feasible saturated quota in the coefficient comparison.

- On a regular profile, $`A=\sum_i p_i(1-p_i)=n x(1-x)-B`$, with $`B\le n\eta^2`$, so its exact precision satisfies $`\Lambda=dA/(d-1)\ge d/5`$. The cumulant, Gaussian, and coefficient coupling estimates in the direct comparison require this bound and $`d\ge n^{.99}`$. The additional determinant variation obeys $`25\eta^2/s\le25n^{-.49}`$. [Fixed-profile comparison](direct-comparison.md)
- For the row-conditioned tail, $`\eta\le\min(s,1/4)/12`$, $`n/(2T^2)\ge10`$, $`A-n/d\ge n/(2T)`$, and $`\log(2\pi n)<n/(4T^2)`$. In particular $`A\ge n/T`$ and $`n/d\le T`$. Both $`n^2/(4T^2)`$ and $`n^{1/5}/(40T^2)`$ exceed $`1000(T^2+u)`$. For the second inequality use $`n^{1/5}/(40T^2)\ge e^{.18u}/(40\cdot400^2)`$ and $`1000(T^2+u)\le10^3(400^2+u)e^{.02u}`$. The lower endpoint and then monotonicity of the ratio verify the comparison. These estimates absorb the stated Bessel, mean-atom, and Gaussian normalization costs. [Row-conditioned tail](direct-row-tail.md)
- The regular scalar second moment has bound $`100(nd+1)e^{20/s}`$. On the event that only the other profile in the coupling is irregular, the Cauchy–Schwarz relative loss is bounded by $`80\sqrt{2n(nd+1)e^{-2d\eta^2}\cdot100(nd+1)e^{20/s}}`$. The log of this bound is $`O(u)-d\eta^2+10/s`$, with $`d\eta^2\ge e^{.49u}`$ and $`10/s\le10 e^{.01u}`$. It is below $`1/(2n)`$, as is the self-irregular loss $`2n^2e^{-d\eta^2/2}`$. Thus $`n^{-1/6}`$ for the regular pair and $`4/n`$ for restoring mass still give the claimed $`n^{-1/8}`$. The polynomial bound on the second moment from the logarithmic-aspect proof is unnecessary.

The orientation bound gives $`b_k\ge d/(k+1)+d/(n-k+1)`$. Thus for $`b_k\le\log4`$ the adjacent edges have enough room in the density strip before any deficit estimate is used. The $`d`$-step negative-binomial curvature bound applies to the two adjacent scalar coefficients at an internal quota, including a saturated one. Together with the coefficient comparison and the curvature of its baseline $`L_k`$, it forces $`h=nr/d-k>\sqrt n/2`$. Here $`1+1/s\le1+n^{.01}`$ suffices in the deficit denominator. The window of radius $`J+2\le u+4`$ is then feasible and strictly interior in mean, has densities in the strip, and has deficits at least $`\sqrt n/4`$. The carried-load inequality gives $`V\ge s^2\sqrt n/32`$ there. At full cap $`r=d`$ the binomial variance gives the same bound directly. [Deficit comparison](https://github.com/ProgramComputer/open-math-research/blob/a001b49093c70856381e2b48a6204e3fac5a2ca7/topics/balanced-arrays/deficit-curvature/scalar.md) · [Carried-load variance](https://github.com/ProgramComputer/open-math-research/blob/27e3e70d6603e8a395c5fdb7ff944922bce83380/topics/balanced-arrays/engset-curvature/carried-load.md)

For $`b_k\ge100/u`$ with $`b_k\le\log4`$, the theta comparison uses its local hypothesis $`\lambda_\theta=50/u\le b_k/2`$. Its scalar error estimates still use the actual lower aspect $`s`$. The two displayed height inequalities hold, as does $`64/(ns^2)<\epsilon_\theta/16`$. On the remaining window $`b_k<100/u`$, the orientation bound gives

$$
k(n-k)>\frac{du(n+2)}{100}-(n+1),\qquad
\frac{nx(1-x)}d>\frac u{200}.
$$

The triangle-kernel entropy curvature has weight $`ns^2`$. Its difference from $`b_k`$ is less than $`1/u`$: the atom prefactor contributes at most $`2\cdot10^9/\sigma_{\min}`$ by the mean-parameter Lipschitz estimate, the LLT log errors contribute at most $`4\cdot10^{11}n^{-1/4}`$, and the neighboring errors and baseline cost at most $`2n^{-1/8}+10/(ns^2)`$. It follows that some mean a distance at most $`s`$ from the center has $`V\ge ns^2 u/101`$. Moving back to the center costs at most $`10^9s`$ in standard deviation and gives $`nV/d^2>u/110`$. In particular the earlier $`\sigma_{\min}\ge s n^{1/4}/\sqrt{32}`$ justifies using the derivative estimate throughout the interval in this bootstrap. [Theta window](theta-window.md) · [Scalar LLT and derivative](../adjacent-quotas/scalar.md)

## Neighboring coefficients and phase

Let $`w`$ be the positive center tilt of mean $`\mu=dx`$, $`\theta=\log w`$, $`v=t_k^{1/d}`$, and $`\Delta=\log(v/w)`$. Write $`\nu=(d-1)/2`$, $`g(x)=\log(x(1-x))`$, and $`t_{\ast}=\pi/d`$. At quota $`k+j`$, $`\log a_{k+j}`$ has terms $`nf(\mu+js)`$, the log of the scalar mean atom, $`-\nu g(x+j/n)`$, a common constant, and the log correction of the neighbor comparison. Here $`f'(m)=-\log w(m)`$. The difference of the correction terms at $`j=-1,1`$, divided by two, costs at most $`n^{-1/8}`$ by the two consecutive estimates. The factor $`1/2`$ is essential. The negative half forward difference is $`\log t_k`$, giving

$$
d\Delta=\frac{\nu}{n}g'(x)+E,\qquad |E|\le4n^{-1/8}.
$$

For the constants, throughout the short mean interval $`\sigma\ge n^{.49}/2`$ since the center has $`\sigma\ge n^{.49}`$ and the mean change is at most $`s\le1`$. Hence $`|f'''|\le16\cdot10^9 n^{-1.47}`$ and the symmetric difference of $`nf`$ has error at most $`10^{10}n^{-.47}`$. The atom log difference costs at most $`4\cdot10^9 n^{-.49}+10^{11}n^{-1/4}`$. The baseline error costs at most $`5/(ns)`$ since $`|g''|\le18/s^2`$ in the strip. These are all smaller than the asserted error allowance. In particular $`|d\Delta|\lt3`$ and $`|\Delta+it_{\ast}|\lt8/d`$.

At the center law put $`X=S-\mu`$, $`a=\mathbb E q_S`$, $`c=\mathrm{Cov}(q_S,S)`$, with $`q_j=j(d-j)/(d(d-1))`$. For $`z=\Delta+it_{\ast}`$, expand $`\psi(z)=\mathbb E e^{zX}`$ and $`\mathbb E[q_S e^{zX}]/\psi(z)`$. The respective logarithms after removing their values at zero have leading terms $`Vz^2/2`$ and $`cz/a`$. To check the errors, $`|X|\le d`$, $`\mathbb E|X|^3\le10^9\sigma^3`$, $`V\le d/4`$, and $`a\ge x(1-x)\ge s/5`$. On $`|z|\le8/d`$, Taylor expansion with $`|e^{zX}|\le e^8`$ gives $`|\psi-1|\le10^5n/d^2`$ and cubic error at most $`10^{15}n^{3/2}/d^3`$. Also $`|c|\le2V/d`$. The numerator after removing $`a\psi`$ has linear term $`cz`$ and a remainder bounded by $`3\cdot10^{14} n^{3/2}/d^3`$, using

$$
\mathbb E[|q_S-a||X|^2]\le (2/d)(\mathbb E|X|^3+\sigma V).
$$

Dividing by $`a\psi`$ and expanding the log costs at most $`10^{16}n^{-1.46}`$ in the latter normalized expression. Both ratios are within $`1/2`$ of one on the disk, so these logarithms give the required continuous phases from the real tilt. In particular the angular error bounds $`10^{16}n^{-.47}`$ and $`10^{17}n^{-.46}`$ in the calibration check out.

Their potentially order-one terms enter the total with opposite signs. The quadratic function $`q`$ gives the exact identities

$$
a=\frac{d^2x(1-x)-V}{d(d-1)},\qquad
c=\frac{d(1-2x)V-\kappa_3}{d(d-1)},\qquad
\kappa_3=\mathbb E X^3 .
$$

After inserting the displacement, the residual before multiplication by $`\nu t_{\ast}`$ is exactly

$$
\frac{V}{d}g'(x)-\frac ca
=\frac{\kappa_3}{d^2x(1-x)-V}
-\frac{V^2(1-2x)}{d x(1-x)[d^2x(1-x)-V]}.
$$

The bounds $`V\le dx(1-x)`$ and $`x(1-x)\ge s/5`$ control the two terms by $`10^{10}n^{-.47}`$ and $`1/(d-1)`$, respectively. The displacement error costs at most $`4n^{-.115}`$, since $`nVt_{\ast}/d\le n^{.01}`$. Together these give the claimed phase deviation below $`n^{-1/10}`$, with no choice of a wrapped argument.

## Transfer to the geometric tilt

Use a subscript $`\xi`$ for the row law at the real tilt $`we^\xi`$, along the segment from $`0`$ to $`\Delta`$. The likelihood ratio with the center law lies between $`e^{-d|\xi|}`$ and $`e^{d|\xi|}`$ because the support is in $`[0,d]`$. Taking the infimum of $`\mathbb E_\xi(S-m)^2`$ over all real $`m`$ therefore gives $`e^{-3}V_0\le V_\xi\le e^3V_0`$. This step only ensures that the entire segment has $`\sqrt{V_\xi}\ge e^{-3/2}n^{.49}>10^4`$. The moment estimate now gives the sharper bound

$$
\left|\frac{\mathrm d}{\mathrm d\xi}\log V_\xi\right|
=\frac{|\kappa_{3,\xi}|}{V_\xi}
\le10^9\sqrt{V_\xi}\le \frac{10^9}{2}\sqrt d,\qquad
\left|\log\frac{V_\Delta}{V_0}\right|\le\frac{1.5\cdot10^9}{\sqrt d}.
$$

Write $`a_\xi=\mathbb E_\xi q_S`$ and $`x_\xi=\mathbb E_\xi S/d`$. The all-tilt variance bound and the same covariance estimate give $`a_\xi\ge x_\xi(1-x_\xi)\ge V_\xi/d`$ and $`|a'_\xi|\le2V_\xi/d`$. Thus $`|\log(a_\Delta/a_0)|\le6/d`$. Likewise $`|[\log(x_\xi(1-x_\xi))]'|\le1`$ by $`x'_\xi=V_\xi/d`$ and the variance bound. In particular

$$
\frac{n V_\Delta}{d^2}>\frac{u}{111},\qquad
\frac{n a_\Delta}{d}>\frac{u}{201},\qquad
\frac{n x_\Delta(1-x_\Delta)}d>\frac{u}{201}.
$$

For the $`q`$-weighted radial law, put $`\widetilde p_\xi(j)=q_j p_\xi(j)/a_\xi`$. Its variance satisfies the exact relation

$$
\widetilde V_\xi
=V_\xi+\frac{\mathrm{Cov}_\xi(q_S,(S-\mu_\xi)^2)}{a_\xi}
-\left(\frac{\mathrm{Cov}_\xi(q_S,S)}{a_\xi}\right)^2 .
$$

The same weighted moment bound used in the phase calculation and $`a_\xi\ge V_\xi/d`$ give $`|\widetilde V_\xi/V_\xi-1|\le 2(10^9+1)/\sqrt{V_\xi}+4/V_\xi`$. In particular this variance is between $`V_\xi/2`$ and $`2V_\xi`$ on the whole real segment. Its law is also a one-step shift of a capped binomial on $`d-2`$ coordinates, since $`q_j\binom dj=\binom{d-2}{j-1}`$. At full cap use the actual nonzero support $`1,\ldots,d-1`$.

## Near nonprincipal leading terms

The transferred constants suffice for an explicit suppression of nonprincipal *Gaussian terms* in one near band. At the geometric tilt write $`V=V_\Delta`$, $`\sigma=\sqrt V`$, and $`\phi(\tau)=\mathbb E_\Delta e^{i\tau S}`$, with $`\widetilde\phi`$ for the weighted law. For $`D=S-S'`$ with independent copies, $`|\phi|^2=\mathbb E\cos(\tau D)`$ and $`\mathbb E|D|^3\le 8\cdot10^9\sigma^3`$. For $`0\le\tau\le(8\cdot10^9\sigma)^{-1}`$, Taylor's bound $`|\sin y-y|\le y^2/2`$ gives $`\mathbb E[D\sin(\tau D)]\ge V\tau`$. Since $`|\phi|^2\le1`$ and stays positive on this band,

$$
\left|\frac{\phi(\tau)}{\phi(t_{\ast})}\right|
\le \exp\negthinspace{}\bigl[-V(\tau^2-t_{\ast}^2)/4\bigr]
\qquad (t_{\ast}\le\tau\le(8\cdot10^9\sigma)^{-1}).
$$

In the same band, the variance cosine bound gives $`|\widetilde\phi(\tau)|\ge1-\widetilde V_\Delta\tau^2/2`$. After centering each characteristic function at its own mean, its distance from one is at most half its variance times $`\tau^2`$. The means differ by at most two, so the ratio $`\widetilde\phi(\tau)/\phi(\tau)`$ stays in the right half-plane. The determinant amplification $`|\phi(\tau)/\widetilde\phi(\tau)|^\nu`$ is at most $`\exp(2d V\tau^2)`$. For $`|\tau|=j t_{\ast}`$ with odd $`j\ge3`$, use $`\tau^2\le(9/8)(\tau^2-t_{\ast}^2)`$ and $`n/d>u/201>18`$ to absorb this into half the preceding gap after raising $`\phi`$ to its $`n`$th power. The principal determinant is bounded above and below by fixed positive constants, since $`d Vt_{\ast}^2\le\pi^2/4`$. The near nonprincipal terms, summed in principal radial units, are bounded by

$$
2\sum_{m\ge0}\exp\left[-\frac{\pi^2 u}{888}\big((3+2m)^2-1\big)\right].
$$

This comparison avoids assuming that the variances at the two real tilts are identical. It is an estimate for the near Gaussian terms. A sign for the coefficient polynomial still requires the corresponding errors for the actual angular integrals and bounds on contributions from outside this band. Existing arguments with unspecified cutoff constants cannot on their own assert that sign throughout the stated finite strip.
