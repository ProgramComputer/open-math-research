# Sparse fixed-profile transfer and the complete finite upper band

2026-11-26 · Private research note

Let $`d\to\infty`$ and $`b=d^2/n\to\infty`$ with $`b=o(d)`$. Thus $`n/d\to\infty`$ and eventually $`n\le d^2`$. Let $`1\le c=d-r`$ with $`c/b\to\gamma<\infty`$, and let $`a_k`$ be the balanced-array coefficient. Write $`T=nr/d`$, $`D=\lfloor T\rfloor`$, $`j=D-k`$, and $`t_k=\sqrt{a_{k-1}/a_{k+1}}`$ at an internal quota.

This note assumes the sparse fixed-profile estimate

$$
\Pr(\text{equal column sums}\mid\vec s)
=\sqrt d\thinspace (2\pi\Lambda_{\vec s})^{-(d-1)/2}
\exp\left[-\frac1{12B}+o(1)\right],
\qquad
\Lambda_{\vec s}=\sum_i\frac{s_i(d-s_i)}{d(d-1)},
\tag{1}
$$

uniformly over profiles with total $`d\ell`$, $`\ell/d\to B\in(0,\infty)`$ and maximum row size $`o(d)`$. The row subsets in this probability are independent and uniform at their prescribed sizes. Subject to (1), every internal quota with $`j=O(d)`$ has the strict sign $`(-1)^k`$ at $`-t_k`$. If $`j/d\to\beta>0`$, the first angular crossing $`v_k`$ of $`k\pi`$, and indeed every crossing, satisfies $`\log(v_k^d/t_k)=o(1)`$ and has the same sign. No degree-product condition enters this transfer.

## Relative margin summation

Complement the arrays into holes. Write $`\ell=n-k`$, $`m=d\ell/n=c+h`$, $`p=\ell/n`$, and

$$
G(w)=\sum_{s=c}^d\binom ds w^s,\qquad U_\ell=[w^{d\ell}]G(w)^n.
$$

Because $`\ell/d=c/b+j/d+O(1/d)`$ is bounded, either $`\ell/d\to0`$ along a subsequence, or we may pass to $`\ell/d\to B>0`$. In the first case normalized coefficient curvature gives $`\log\Gamma_k\ge d\log(1+1/\ell)\to\infty`$ for $`\Gamma_k=a_k^2/(a_{k-1}a_{k+1})`$. This alone gives the geometric sign by the alternating-tail bound below. In the second case $`\ell\asymp d`$, $`m\asymp b`$, and $`p=o(1)`$, including at bounded available shifts.

For $`m>c`$ let $`X`$ have the tilted weights $`\binom ds w_\ell^s`$ on $`c\le s\le d`$, with $`\mathbb E X=m`$ and variance $`V`$. It is an unrestricted binomial tilt with parameter $`w_\ell/(1+w_\ell)`$ conditioned on size at least $`c`$. The unrestricted mean is at most $`m`$, so $`dw_\ell=O(m)`$, and the mass ratio at the step to size $`s`$ is at most $`Cm/s`$. At $`m=c`$ use the deterministic law at $`c`$. These bounds give $`\mathbb E X^q=O_q(m^q)`$, since the ratios are at most one half beyond a large fixed multiple of $`m`$, and the sizes before then are $`O(m)`$.

In the actual balanced hole arrays, let $`A_s`$ count those with specified row size $`s`$. If $`s>c`$, move a hole from that row to a different row in the same column. There are exactly $`s(n-\ell)`$ possibilities, and at most $`(d-s+1)\ell`$ reverse moves, whether or not the reverse donor can spare its hole. Therefore $`s(n-\ell)A_s\le (d-s+1)\ell A_{s-1}`$. Its mass ratio is at most $`m/[(1-p)s]`$. Both the actual and candidate row laws consequently have tails smaller than any prescribed inverse power of $`n`$ above $`L=\lceil A(m+\log n)\rceil`$ for sufficiently large fixed $`A`$. The same holds for fixed moments of their tails. Removing actual arrays with any row above $`L`$ costs a relative $`o(1)`$ by the union bound. Note that $`L=o(d)`$.

Under independent candidate rows, condition on $`\mathcal E=\{\sum_iX_i=d\ell\}`$. The profile probabilities are proportional to $`\prod_i\binom d{s_i}`$ with normalizing sum $`U_\ell`$. The conditioning event has probability at least $`1/(nd+1)`$: the sum pmf $`f`$ is log-concave with interval support by convolution, so Jensen at its integer mean on the piecewise-linear interpolation of $`\log f`$ yields $`\log f(d\ell)\ge\mathbb E\log f(\sum_iX_i)\ge-\log(nd+1)`$. The deterministic case is immediate. Thus candidate profiles with any row above $`L`$ also have conditional weight $`o(1)`$.

For a retained profile put $`R=n^{-1}\sum_i(s_i-m)^2`$ and $`\nu=(d-1)/2`$. The exact identity

$$
\Lambda_{\vec s}
=\Lambda_0\left(1-\frac{R}{m(d-m)}\right),\qquad
\Lambda_0=\frac{\ell(d-m)}{d-1},
$$

follows by expanding $`\sum_i s_i(d-s_i)`$. On retained profiles, $`R\le Lm`$ since $`s_i^2\le Ls_i`$. Hence the weight $`(\Lambda_{\vec s}/\Lambda_0)^{-\nu}`$ is at most $`e^{O(L)}`$, which may be superpolynomial. We next control its conditional expectation.

A binomial law conditioned to be at least $`c`$ has variance at most its mean, at every real exponential tilt. Indeed its relative likelihood to the binomial law with the same mean is geometric on its interval support. The signed mass difference is positive on an interval and negative outside. Equal total mass and mean allow subtraction of a chord from a convex test function, proving convex-order domination. If $`\mu_t`$ denotes the mean after real tilt by $`e^{tX}`$, then $`\mu_t'\le\mu_t`$. Integration gives $`\mu_t\le m e^t`$ for $`t\ge0`$ and $`\mu_t\ge m e^t`$ for $`t\le0`$. Integrating these inequalities in their respective directions proves

$$
\log\mathbb E e^{t(X-m)}\le m(e^t-1-t)
$$

for every real $`t`$. Thus $`\Pr(|X-m|\ge u)\le2\exp[-c\min(u^2/m,u)]`$ by exponential Markov.

Define the clipped variable $`W=(X-m)^2/m`$ on $`X\le L`$, and set it to zero otherwise. Its mean differs from $`V/m`$ by an arbitrarily small inverse power of $`n`$ by the tail estimate. If $`m\ge\log n`$ then $`L=O(m)`$, so the displayed Bernstein-type bound gives $`\Pr(W>x)\le2e^{-c_A x}`$ for all $`x\ge0`$. The range above a fixed multiple of $`m`$ has probability zero, and below it the two alternatives in the Bernstein exponent are each at least a constant times $`x`$. Consequently $`W`$ has a uniform positive exponential moment and its centered log moment generating function is $`O(t^2)`$ in a fixed interval around zero. With tolerance $`\epsilon=(L/n)^{1/4}=o(1)`$, exponential Markov gives deviation probability $`\exp[-\Omega(n\epsilon^2)]`$ for its sample mean. Here $`n\epsilon^2=\sqrt{nL}\gg L+\log(nd)`$ because $`L=o(d)`$ and $`n/d\to\infty`$.

If $`m\le\log n`$, then $`L=O(\log n)`$ and $`W=O(L^2/m)`$. At tolerance $`n^{-1/10}`$, Hoeffding gives deviation probability $`\exp[-\Omega(n^{4/5}m^2/L^4)]`$, again with exponent dominating $`L+\log(nd)`$. In both cases, dividing by $`\Pr(\mathcal E)`$ and multiplying by the maximal weight $`e^{O(L)}`$ leaves the bad retained profiles negligible. On the other retained profiles, $`R/m=V/m+o(1)`$ and $`V/m\le1`$. Therefore

$$
-\nu\log\left(1-\frac{R}{m(d-m)}\right)
=\frac{(d-1)V}{2m(d-m)}+o(1)
$$

uniformly there. Applying (1) on the retained profiles and using the actual relative tail bound proves

$$
a_k=\mathcal K(\ell) U_\ell
\exp\left(\frac{(d-1)V}{2m(d-m)}-\frac1{12B}+o(1)\right),
\qquad
\mathcal K(\ell)=\sqrt d\thinspace(2\pi\Lambda_0)^{-\nu}.
\tag{2}
$$

This applies uniformly under bounded available shifts. At saturation $`R=V=0`$ deterministically, and the same formula follows directly. The correction exponent other than $`\log\mathcal K+\log U_\ell`$ is bounded. Moreover $`\log\mathcal K(\ell+1)-\log\mathcal K(\ell)=-d/(2\ell)+o(1)`$, since $`\Lambda_0=\ell(d-m)/(d-1)`$, the second factor changes logarithm by $`O(1/n)`$ per shift, and $`\ell\asymp d`$. The second difference is $`o(1)`$.

## Scalar shape and all finite upper signs

In addition to $`V\le m`$, the excess $`X-c`$ has variance at most $`h(1+h)`$ by the same relative log-concavity and equal-mean convex-order comparison with a geometric law. The log-concave lattice moment inequality $`\mathbb E|X-m|^3\le CV(1+\sqrt V)`$ and differentiation in log tilt give $`|dV/dm|\le C(1+\sqrt V)`$. In particular $`\sqrt{1+V}`$ is uniformly Lipschitz as a function of $`m`$. A bounded quota shift changes $`m`$ by $`O(b/d)=o(1)`$, so it changes $`\sqrt{1+V}`$ by $`o(1)`$. Thus $`V`$ is relatively stable whenever bounded below, even when its absolute variation need not tend to zero. We use the uniform log-concave lattice local limit at an integer mean, which gives conditioning probability $`(1+o(1))/\sqrt{2\pi nV}`$ whenever $`V`$ is bounded below. [Log-concave local limit and centered-moment estimates](https://github.com/ProgramComputer/open-math-research/blob/78e9ef2c0c0b7a5daed126efbe12a46d030d8200/topics/balanced-arrays/fifth-thirds/subquadratic-scaling-corank-upper.md#scalar-limits-and-stability-at-quota-shifts)

Write $`E(\ell)=n\log G(w_\ell)-d\ell\log w_\ell`$ for the interior real tilt exponent. The tilt equation gives

$$
E'=-d\log w_\ell,\qquad E''=-b/V.
$$

Suppose first that $`j/d\to\beta>0`$, so $`h/b\to\beta`$ and $`m/b\to\gamma+\beta=B`$. Trial an unrestricted binomial mean $`c+\beta b/2`$. Its lower tail below $`c`$ is $`e^{-\Omega(b)}`$ by Chernoff, since its separation from $`c`$ is a fixed fraction of its order-$`b`$ mean. Conditioning changes its mean by $`O(be^{-\Omega(b)})`$, so the resulting mean is less than $`m`$. Monotonicity gives the same order-$`b`$ separation for the actual unrestricted mean. Conditioning at that mean changes raw moments of each fixed order $`q`$ by $`O_q(b^qe^{-\Omega(b)})`$. Hence $`V\sim m`$ as the unrestricted binomial parameter tends to zero, uniformly at bounded real shifts. The local limit expresses $`U_\ell=e^{E(\ell)}(1+o(1))/\sqrt{2\pi nV}`$. Both its prefactor and the correction in (2) vary by $`o(1)`$ in log at fixed shifts. The centered first difference of $`E`$ is $`E'+o(1)`$, since $`E''`$ has a common finite limit on both halves. Together these give

$$
\log\Gamma_{k+i}\longrightarrow 1/B\quad(i\text{ fixed}),\qquad
\log t_k=-d\log w_\ell-d/(2\ell)+o(1).
\tag{3}
$$

If $`j/d\to0`$ and $`\ell/d\to B>0`$, then $`B=\gamma`$. Pass to subsequences in the bounded quantities $`V/b`$ and, where needed, $`h`$.

If $`V/b\to v_*>0`$, then $`V\le h(1+h)`$ forces $`h\gtrsim\sqrt b`$ and $`j\gtrsim d/\sqrt b\to\infty`$, so all fixed neighboring quotas exist. Relative variance stability, (2), and the local limit give $`\log\Gamma_{k+i}\to1/v_*`$ at each fixed offset. Here the correction in (2) has a common finite limit at each shift.

If $`V/b\to0`$ and $`h\ge\eta>0`$, then $`V`$ is uniformly bounded below. Otherwise Chebyshev at very small variance would force one atom to have mass above $`0.9`$. At an interior mode $`s`$, the product of its two adjacent mass ratios is $`s(d-s)/[(s+1)(d-s+1)]\ge1/4`$, which precludes this. At the upper endpoint $`d`$, such a mass contradicts $`m=O(b)=o(d)`$. At the lower endpoint $`c`$, if the first forward ratio is $`q`$, log-concavity and the large modal mass give $`h\le Cq`$ and $`V\ge c_1q`$, contradicting $`h\ge\eta`$ for sufficiently small variance. This lower bound holds also on bounded real shifts, since they change $`h`$ by $`o(1)`$. Relative stability and the local limit give log-prefactor differences $`o(1)`$, while $`E''=-b/V\to-\infty`$ uniformly on the shifts. The correction in (2) again varies by $`o(1)`$, so $`\Gamma_k\to\infty`$.

If $`h\to0`$, put $`e=nh\ge d`$ at an internal quota. Apply the scalar negative-binomial curvature bound to the excess coefficients $`\binom d{c+s}`$. It yields

$$
\log\frac{U_\ell^2}{U_{\ell-1}U_{\ell+1}}
\ge \frac{d(n-1)}{n+e+d-1}\log(1+d/e)
\ge (1-o(1))\frac{b}{h+b/d}\longrightarrow\infty.
$$

The variances at the three quotas tend to zero by $`V\le h(1+h)`$, including a possible saturated neighbor. The small changes of the prefactor and correction in (2) preserve the divergence. [Scalar bound](https://github.com/ProgramComputer/open-math-research/blob/04564a728c21eab6ce511b98a48ccaac754648ff/topics/balanced-arrays/very-tall/very-tall-upper-quota.md#the-last-od-quotas)

For an actual coefficient vector, ratios decrease strictly by normalized log-concavity. At $`t_k`$ both first outward magnitudes relative to the central term are $`\Gamma_k^{-1/2}`$ and the magnitudes decrease outwards. Divergent $`\Gamma_k`$ therefore gives the sign $`(-1)^k`$ by the first-term bound on each alternating tail. If $`\log\Gamma_{k+i}\to C>0`$ for all fixed offsets, the normalized magnitude at offset $`i`$ tends to $`e^{-Ci^2/2}`$. Cut the alternating tails with error at most the first omitted term. Passing first to the quota limit and then to an increasing truncation gives the positive limit $`\sum_{i\in\mathbb Z}(-1)^i e^{-Ci^2/2}`$ by the Gaussian Fourier series. The same proof applies at $`t_ke^{o(1)}`$, since fixed offsets have the same limits and both first outward ratios stay strictly below one. This proves the strict signs along every sequence in the finite upper band.

## Matching the angular points at positive offset

For an occupied tilt $`v`$ let $`X`$ be the hole size under $`w=1/v`$, $`S=d-X`$, $`\mu=\mathbb ES`$, $`y=n\mu/d`$, $`\phi=\pi/d`$, and $`\lambda(X)=X(d-X)/[d(d-1)]`$. The angular phase is

$$
\Psi(v)=n\arg H_{\rm occ}(ve^{i\phi})-\nu\arg a_\phi,\qquad
a_\phi=\frac{\mathbb E[\lambda(X)e^{-i\phi X}]}{\mathbb E e^{-i\phi X}} ,
$$

where $`H_{\rm occ}(v)=\sum_{s=0}^r\binom ds v^s`$. The occupied sums have their arguments in the sector $`[0,r\phi]`$, so the phase is continuous on positive tilts. Its limits at zero and infinity are $`-\nu\phi`$ and $`T\pi`$, giving ordered first crossings.

At any crossing $`\Psi=k\pi`$, the general bound $`|\Psi/\pi-y|\le Cd+C(T-y)/\sqrt d`$ gives $`T-y=O(d)`$, since $`T-k=O(d)`$. For this bound use $`V\le\min(d/4,h(1+h))\le C\sqrt d\,h`$ from convex-order comparisons with the mean-matched binomial and geometric, and use the cubic sine remainder on the centered size characteristic function to bound the row-angle error by $`O(V/d^2)`$. The curvature argument has absolute value at most $`\pi`$ from its two sectors. Thus at the crossing the hole mean $`m=d-\mu=c+d(T-y)/n`$ is $`O(b)`$, although we have not yet separated the hole mean from the cap.

Set $`Z=X-m`$. For the hole tilt at these crossings, the centered log-concave moment bound gives $`\mathbb E|Z|^3\le CV(1+\sqrt V)\le Cm^{3/2}`$. The centered row-angle remainder multiplied by $`n`$ is $`O(nm^{3/2}/d^3)=O(\sqrt b/d)=o(1)`$. For the curvature argument, center the phase in both numerator and denominator at $`m`$. We have

$$
\mathbb E\lambda(X)=m/d+O(m^2/d^2),\quad
\frac{\mathrm{Cov}(\lambda(X),X)}{\mathbb E\lambda(X)}
=\frac Vm+O(m/d).
$$

The second identity uses $`\mathrm{Cov}(X^2,X)=2mV+\mathbb E Z^3`$ and $`V\le m`$. Crucially the relative weighted second centered moment is $`O(m)`$, since

$$
\mathbb E[\lambda(X)Z^2]\le \frac{C}{d}\left(mV+\mathbb E|Z|^3\right)
=O(m^2/d).
$$

Thus Taylor of the centered weighted characteristic quotient gives $`\arg a_\phi=-(V/m)\phi+O(\phi m/d+\phi^2m)=-(V/m)\phi+o(\phi)`$. This uses only $`m=O(b)=o(d)`$, with $`m\ge c\ge1`$. Consequently every crossing satisfies

$$
\Psi/\pi=y+\frac{V}{2m}+o(1),\qquad y=k+O(1).
$$

If $`j/d\to\beta>0`$, then at every crossing $`h/b=(T-y)/d\to\beta`$. The trial-binomial calculation now yields $`V/m\to1`$ there, so $`y=k-1/2+o(1)`$. At $`v_{\rm geo}=t_k^{1/d}`$ the drift formula in (3) shifts the occupied log tilt from $`-\log w_\ell`$ by $`-1/(2\ell)+o(1/d)`$. Since $`dy/d(d\log v)=V/b\to B`$ uniformly on this short interval, this gives the same value $`y(v_{\rm geo})=k-1/2+o(1)`$. The uniformity follows from $`V\le m`$ controlling the change of $`m`$ over an $`O(1/d)`$ log-tilt interval. Strict increase of $`y`$ traps every value between this point and any crossing in that same $`o(1)`$ neighborhood. Consequently $`h/b\to\beta`$ and $`V/b\to B>0`$ throughout the connecting interval, so the mean value theorem gives $`\log(v_k^d/t_k)=o(1)`$. This proves the first crossing statement as well as the perturbative strict sign there.

At an overlap with $`j/d\to\beta>0`$, the adjacent geometric log spacings tend to $`1/B`$ by (3), since the spacing is $`(\log\Gamma_k+\log\Gamma_{k+1})/2`$. Replacing the last inner test point by its first angular crossing preserves the order. This is the finite upper-band transfer conditional on (1); the sparse fixed-profile constant and all remaining bands are separate inputs.
