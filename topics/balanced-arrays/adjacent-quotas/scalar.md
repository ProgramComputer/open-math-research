# Effective variation of scalar quota curvature above the saturation strip

Let $`n\ge10^{200}`$, $`59/200\le d/n\le1`$, and $`1\le r\le d`$.
Put $`\rho=r/d`$, $`D=\lfloor nr/d\rfloor`$, and

$$
U_j=[z^{dj}]\left(\sum_{s=0}^r\binom ds z^s\right)^n,
\qquad a_j=U_jQ_j,\qquad
L_j=[2\pi n x_j(1-x_j)]^{-(d-1)/2},
\qquad x_j=j/n,
$$

where $`a_j`$ is the actual balanced-array count and $`Q_j`$ is the probability of
column balance when restricted rows are independently counted subject to
their total. Write $`\Gamma_j=a_j^2/(a_{j-1}a_{j+1})`$ and $`E_j=\log(Q_j/L_j)`$.

Suppose $`x_k\in[.30,.70]`$, $`h=nr/d-k\ge .4\sqrt{n/\log n}`$, and
$`\Gamma_k\le4`$. If $`|E_{j+1}-E_j|\le10^{-6}`$ for $`k-2\le j\le k`$,
then $`\Gamma_{k-1}\le1.001\Gamma_k`$. If the same bound holds also at
$`j=k+1`$, then $`\Gamma_{k+1}\le1.001\Gamma_k`$. All quota indices used are
strictly within the support under the stated density and deficit conditions.


## An explicit scalar local limit estimate

The following quantitative restricted version of the
[uniform lattice estimate](../dense-regime/uniform-lattice-lemma.md) suffices.
Let $`X`$ have a finite log-concave mass function with integer interval
support, mean $`\mu`$ and standard deviation $`10^4\le\sigma\le n`$.
If $`n\ge10^{200}`$ and $`n\mu`$ is an integer, then for the sum of $`n`$
independent copies,

$$
\left|\log\Pr\left(\sum_iX_i=n\mu\right)
+\tfrac12\log(2\pi n\sigma^2)\right|\le 10^{11}n^{-1/4}.
$$

For the same family under an interior exponential tilt,
$`|d\sigma/d\mu|\le 10^9`$.

Choose a mode $`m`$ and let $`b=\Pr(X=m)`$. Chebyshev's inequality on the interval
of radius $`2\sigma`$ about $`\mu`$ gives $`b\ge1/(8\sigma)`$. On either side of
the mode the first crossing of $`b/2`$ lies at distance at most $`3/b`$,
including a zero immediately outside the support if necessary. Concavity of
the log mass beyond that crossing and the modal bound before it give

$$
\Pr(X=m\pm j)\le2b\exp(-bj/5)\qquad(j\ge0).
$$

In fact the usual bound has rate $`b\log 2/3>b/5`$. For any positive integer
$`q`$, $`\sum_{j\ge1}j^q e^{-u j}\le e^u q!/u^{q+1}`$ by comparison with the
integral over intervals $`[j,j+1]`$. With $`u=b/5`$, this gives
$`\mathrm{Var}(X)\le2000/b^2`$ and
$`\mathbb E|X-m|^3\le30000/b^3`$. Centering the latter costs at most a factor
eight by Jensen, so $`b\le100/\sigma`$ and
$`\mathbb E|X-\mu|^3\le10^9\sigma^3`$.
For an exponential tilt in parameter $`\eta`$, one has
$`d\mu/d\eta=\sigma^2`$ and $`d\sigma^2/d\eta=\mathbb E(X-\mu)^3`$.
Dividing proves the Lipschitz bound on $`\sigma`$.

For the centered characteristic function $`\phi(t)`$ on $`[-\pi,\pi]`$,
retain the sites within $`2\sigma`$ of $`\mu`$ with mass at least
$`1/(24\sigma)`$. There are at most $`6\sigma`$ sites in the interval, so
the retained sites have probability at least $`1/2`$. Log-concavity
makes them a contiguous block of length $`M\ge\sigma/200\ge50`$.
Using this block in the independent-pair cosine identity gives

$$
1-|\phi(t)|^2\ge (M/(24\sigma))^2(1-|U_M(t)|^2),
\qquad
U_M(t)=M^{-1}\sum_{j=0}^{M-1} e^{ijt}.
$$

For $`|t|\ge2\pi/M`$, the sine quotient bounds $`|U_M(t)|\le1/2`$.
For $`|t|\le2\pi/M`$, at least $`M^2/32`$ ordered pairs in one direction
have distance between $`M/8`$ and $`M/4`$. Their angles have modulus
at most $`\pi/2`$, and $`1-\cos u\ge u^2/5`$ there. Thus
$`1-|U_M(t)|^2\ge M^2t^2/10240`$ on this interval.
Using $`M/\sigma\ge1/200`$ in both cases gives the deliberately weakened bound

$$
|\phi(t)|\le \exp[-10^{-18}\min(\sigma^2t^2,1)].
$$

In Fourier inversion put $`y=\sigma\sqrt n\,t`$. For
$`|y|\le n^{1/12}`$, the third moment and the log series at one show

$$
|n\log\phi(t)+y^2/2|\le 2\cdot10^9 n^{-1/4}.
$$

Indeed the contribution from the cubic Taylor bound is at most
$`10^9 n^{-1/4}`$. Also $`|\phi(t)-1|\le y^2/n<1/2`$ there, so the
quadratic remainder of the log series is at most $`y^4/n\le n^{-2/3}`$
after multiplying by $`n`$. Therefore the scaled integrand on the central
interval differs from the Gaussian by at most $`4\cdot10^9 n^{-1/4}`$
times the Gaussian. The remaining characteristic-function integral,
in the same scaled units, is at most
$`7n^{3/2}\exp(-10^{-18}n^{1/6})`$, since $`\sigma\le n`$.
The omitted Gaussian tail is at most $`2\exp(-n^{1/6}/2)`$.
For $`n\ge10^{200}`$, $`10^{-18}n^{1/6}>4\log n`$ at the lower endpoint
and thereafter by monotonicity of $`n^{1/6}/\log n`$.
Comparing to the full Gaussian integral and taking a logarithm proves
the stated numerical estimate.

## Rate curvature and its variation

Tilt the row size at a real mean $`\mu`$ using the generating polynomial
$`G(z)=\sum_{s\le r}\binom ds z^s`$. The tilted mass is log-concave,
since its successive ratios are the ratios of the binomial coefficients
times the common factor $`z`$. Write $`V(\mu)=\sigma(\mu)^2`$ and
$`\Phi(\mu)=\log G(z)-\mu\log z`$ at this tilt. Then
$`\Phi''(\mu)=-1/V(\mu)`$ by the mean derivative identity.
For the real means in the interval $`[d(k-2)/n,d(k+2)/n]`$, the
variance comparison below
gives

$$
V(d x)\ge d x\frac{\rho-x}{\rho}\ge .04 h.
$$

For the first inequality compare $`S`$ with a binomial of $`r`$ trials of the same mean. On $`0,\ldots,r`$ the ratio of the tilted masses to the binomial masses has consecutive ratios proportional to $`(d-s)/(r-s)`$ and hence is log-convex. The set where the first mass is below the second is an interval. Subtract an affine secant of the convex test function across that interval, placing the endpoints between adjacent sites. The remaining signs and equality of means show that $`S`$ dominates this binomial in convex order. Equivalently for variance alone one can use the quadratic $`(s-a)(s-b)`$ with its sign changes at the endpoints. Identical laws give equality. This proves $`V\ge dx(1-dx/r)`$. [Carried-load derivation and references](https://github.com/ProgramComputer/open-math-research/blob/8a0a986e6baeed69b30de189e75c02fd2c8cb955/topics/balanced-arrays/engset-curvature/carried-load.md)

For the last inequality use $`x\ge .29`$, $`\rho\le1`$, $`d/n\ge .295`$,
and the fact that each local deficit in quota units is at least $`h-2\ge h/2`$.
For $`n\ge10^{200}`$, $`h\ge n^{1/3}`$, using monotonicity of
$`n^{1/6}/\sqrt{\log n}`$. Thus all these standard deviations exceed
$`n^{1/8}\ge10^4`$ and are at most $`d\le n`$ by support size.
The explicit local limit estimate applies at integer quotas and the
Lipschitz bound on $`\sigma`$ applies throughout the entire real mean interval.

Write $`s=d/n`$ and $`\mu_j=dj/n`$. The tilted counting identity and local
limit estimate give

$$
\log U_j=n\Phi(\mu_j)-\tfrac12\log(2\pi n V(\mu_j))+\varepsilon_j,
\qquad |\varepsilon_j|\le10^{11}n^{-1/4}.
$$

The positive entropy contribution to logarithmic curvature at $`j`$ is

$$
B_j=n\int_{-s}^s\frac{s-|t|}{V(\mu_j+t)}\thinspace{}dt .
$$

The remaining scalar contribution has absolute value at most
$`2\cdot10^9 n^{-1/8}+4\cdot10^{11}n^{-1/4}`$, by the Lipschitz bound
on $`\sigma`$, the lower bound $`\sigma\ge n^{1/8}`$, and $`s\le1`$.
The curvature contribution from $`\log L`$ is at most $`50/n`$ in
absolute value, since throughout the interval both $`x`$ and $`1-x`$
exceed $`.29`$ and
$`|[\log(x(1-x))]''|=x^{-2}+(1-x)^{-2}`$.
The error from $`E`$ in the log curvature is at most $`2\cdot 10^{-6}`$
where the two adjacent slope assumptions hold.
Consequently

$$
|\log\Gamma_j-B_j|<3\cdot10^{-6}
$$

at $`j=k,k-1`$ and, if the last slope assumption is available, at $`k+1`$.

At the difficult center, $`B_k<\log 4+3\cdot10^{-6}<1.4`$.
The integral has total weight $`ns^2`$, so its maximum variance on the
center interval is at least $`ns^2/1.4`$. This implies that
$`\sigma>.24\sqrt n`$ somewhere on that interval.
Every point in the full local mean interval is within $`3s\le3`$
of that point, so there $`\sigma\ge .24\sqrt n-3\cdot10^9>.23\sqrt n`$.
Therefore

$$
\left|\frac{d}{d\mu}\frac1{V(\mu)}\right|
\le\frac{2\cdot10^9}{(.23\sqrt n)^3}<2\cdot10^{11}n^{-3/2}.
$$

Translate the entropy integral by one mean step of length $`s`$ and use this
derivative bound. It gives $`|B_{k\pm1}-B_k|<2\cdot10^{11}/\sqrt n`$.
Combining the error bounds yields
$`|\log\Gamma_{k\pm1}-\log\Gamma_k|<10^{-5}<\log(1.001)`$
for each of the tested neighbors.

## Signs at geometric nodes

A difficult center lies in $`.305n<k<.695n`$:
the baseline orientation bound and
$`\log(1+1/u)\ge1/(u+1)`$ would otherwise give

$$
\log\Gamma_k\ge .295
\left(\frac1{.305+1/n}+\frac1{.695+1/n}\right)>1.39>\log4 .
$$

Thus there is room for both neighboring quotas in $`[.30n,.70n]`$, and
the condition on $`h`$ gives room for the next three indices. Suppose the slope bounds in the statement hold.
The global baseline also gives $`\Gamma_j>3.2`$ at every internal quota,
using $`4d/(n+2)\le\log g_j`$ for the binomial baseline $`g_j`$.
At a difficult center the comparison just proved gives
$`\Gamma_{k\pm1}\le1.001\Gamma_k`$.
With $`\tau=1/\sqrt{\Gamma_k}<.56`$, the geometric-node compensation
formula then bounds the normalized signed value below by

$$
1-2/\sqrt{\Gamma_k}+1.88/\Gamma_k^2.
$$

Indeed at $`t_k=\sqrt{a_{k-1}/a_{k+1}}`$ the first neighbors have magnitude $`\tau`$ relative to the center, the second neighbors have magnitude $`\tau^2/\Gamma_{k\pm1}`$, and the ratios from second to third are $`\tau/(\Gamma_{k\pm1}\Gamma_{k\pm2})`$. Subsequent terms decrease because every curvature exceeds one. The alternating tail beyond the third has nonnegative net contribution on each side. Each second term less the corresponding third is at least $`\tau^2(1-.56/3.2^2)/(1.001\Gamma_k)`$. The displayed expression is increasing past $`3.2`$, since
$`3.2^{3/2}>3.76`$, and positive at $`3.2`$ by squaring its equivalent
inequality with positive sides. The normalized value is strictly positive at each such center. The [assembly of the argument](README.md) supplies the slope hypotheses.

The rational numerical comparisons replay from this directory with
`python3 -B scalar-constants.py`. The monotonic comparisons in $`n`$ above
reduce their controls to the displayed lower endpoint.
