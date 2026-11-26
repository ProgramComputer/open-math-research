# Phase calibration at a geometric node

Assume the hypotheses of [the angular overlap reduction](angular-overlap.md):
$`u=\log n\ge10^6`$, $`n^{.99}\le d\le n`$, and $`k`$ is an internal
quota with $`b_k<100/u`$. Use its adjacent coefficient comparison
with error $`n^{-1/8}`$, and its variance conclusion
$`nV/d^2>u/110`$ at the quota tilt. Write $`s=d/n`$, $`x=k/n`$,
$`\mu=dx`$, $`g(x)=\log(x(1-x))`$, and $`\nu=(d-1)/2`$.
Let $`w`$ be the positive tilt giving mean $`\mu`$ for the weight polynomial
$`H(z)=\sum_{j\le r}\binom dj z^j`$. Write $`S`$ for its tilted row size,
$`V=\mathrm{Var}(S)`$, $`\sigma=\sqrt V`$, and
$`\kappa_3=\mathbb E(S-\mu)^3`$.

For the geometric node let $`v=t_k^{1/d}`$ where
$`t_k=\sqrt{a_{k-1}/a_{k+1}}`$. Put $`t=\pi/d`$ and
$`a_v(t)=\mathbb E_v[q_S e^{itS}]/\mathbb E_v e^{itS}`$ with
$`q_j=j(d-j)/[d(d-1)]`$. The arguments are
continuous from zero angular displacement. Then

$$
\left|n\arg H(ve^{it})-\nu\arg a_v(t)-k\pi\right|<n^{-1/10}.
$$

This calibrates the leading term's phase. Estimates for the relative
size of the other angular contributions are separate.

## Scalar displacement

Put $`\theta=\log w`$ and $`\Delta=\log(v/w)`$.
For current mean $`m`$ write $`f(m)=\log H(w(m))-m\log w(m)`$.
Its first three derivatives at interior tilts are
$`-\log w(m)`$, $`-1/V(m)`$, and $`2\sigma'(m)/\sigma(m)^3`$.
Since $`V\le d/4`$ by the capped-binomial variance bound,
the center satisfies $`n^{.49}\le\sigma\le\sqrt n`$ using the
overlap variance lower bound. At the means of $`k\pm1`$ and between,
$`\sigma(m)\ge n^{.49}/2`$ by the overlap interior variance estimates
and the explicit Lipschitz bound $`|\sigma'|\le10^9`$ in
[the scalar estimate](../adjacent-quotas/scalar.md). In particular the whole interval is
inside the domain of that Lipschitz bound. Symmetric Taylor expansion
of $`nf`$ therefore gives

$$
\left|\frac n2[f(\mu+s)-f(\mu-s)]+d\theta\right|
\le 10^{10}n^{-.47}.
$$

Indeed $`\sup|f'''|\le16\cdot10^9 n^{-1.47}`$
and the Taylor error is at most $`ns^3\sup|f'''|/6`$.
The scalar coefficient at mean $`m`$ is $`e^{nf(m)}`$ times the
mean atom of the sum of $`n`$ tilted rows. Half the difference of the
logs of the two atoms is bounded by
$`4\cdot10^9 n^{-.49}+10^{11}n^{-1/4}`$
by the explicit local limit estimate and the variance Lipschitz bound.
The comparison of the balancing factors gives half the difference
of their logs as $`-\nu[g(x+1/n)-g(x-1/n)]/2`$ with error
at most $`n^{-1/8}`$. The overlap ensures both edges are feasible and
their densities lie in $`[s/3,1-s/3]`$. There $`|g''|\le18/s^2`$,
so replacing that half difference of $`g`$ by $`g'(x)/n`$
costs at most $`5/(ns)`$ after multiplication by $`\nu`$.
Inserting these estimates into the geometric-node definition gives

$$
d\Delta=\nu g'(x)/n+E,\qquad |E|\le 4n^{-1/8}.
$$

The bound $`x(1-x)\ge s/5`$ gives $`|\nu g'(x)/n|\le5/2`$.
Thus $`|d\Delta|<3`$ and $`|\Delta+it|<8/d`$.

## The two angular arguments

Use the row law at $`w`$ for both Taylor expansions. Write
$`X=S-\mu`$, $`z=\Delta+it`$, and $`\psi(z)=\mathbb E e^{zX}`$.
The checks below hold on the whole disk $`|z|\le8/d`$, and so
also establish the claimed continuous branches. We have $`|X|\le d`$
and $`\mathbb E|X|^3\le10^9\sigma^3`$ by the scalar moment estimate.
Since $`e^8<3000`$, standard exponential Taylor bounds give

$$
|\psi(z)-1|\le 10^5 n/d^2,\qquad
|\psi(z)-1-Vz^2/2|\le 10^{15}n^{3/2}/d^3.
$$

For example the first estimate uses
$`\mathbb EX=0`$ and $`e^8V|z|^2/2`$; the second uses
$`e^8\mathbb E|X|^3|z|^3/6`$. The elementary logarithm bound
$`|\log(1+y)-y|\le |y|^2`$ for $`|y|\le1/2`$ yields
$`|\log\psi(z)-Vz^2/2|\le 10^{16} n^{-1.47}`$.
Here $`d\ge n^{.99}`$; this makes the square error smaller than the
cubic error. The identity
$`H(we^z)=H(w)e^{\mu z}\psi(z)`$ then gives

$$
n\arg H(ve^{it})=k\pi+nV\Delta t+E_H,\qquad
|E_H|\le10^{16} n^{-.47}.
$$

Put $`a=\mathbb E q_S`$ and $`c=\mathrm{Cov}(q_S,S)`$.
We have $`a=(d^2x(1-x)-V)/[d(d-1)]\ge x(1-x)\ge s/5`$.
The size function $`j\mapsto q_j`$ is $`2/d`$-Lipschitz on $`[0,d]`$.
Centering first at its value at $`\mu`$ shows

$$
|c|\le 2V/d,\qquad
\mathbb E[|q_S-a||X|^2]
\le (2/d)(\mathbb E|X|^3+\sigma V)
\le 3\cdot 10^9 n^{3/2}/d .
$$

In fact the first inequality follows by subtracting $`q_\mu`$ in
$`\mathbb E[q_S X]`$.
Expand the numerator of
$`a(z)=\mathbb E[q_S e^{zX}]/\psi(z)`$ after subtracting $`a\psi(z)`$.
Its remainder from the linear term $`cz`$ is bounded by
$`3\cdot10^{14}n^{3/2}/d^3`$, by the preceding second weighted moment.
Dividing by $`a\psi(z)`$ costs a factor at most $`10n^{.01}`$.
The error from replacing $`1/\psi(z)`$ by $`1`$ in the linear term is
at most $`2|cz/a|10^5 n/d^2`$. Since
$`|cz/a|\le 20n^{-.98}`$, one obtains
$`|a(z)/a-1-cz/a|\le10^{16}n^{-1.46}`$.
In particular the ratio lies in the disk of radius $`1/2`$ about
one. Expanding its logarithm and taking imaginary parts gives

$$
\nu\arg a_v(t)=\nu t c/a+E_a,\qquad |E_a|\le10^{17}n^{-.46}.
$$

The analytic identity $`a(z)=a_v(t)`$ at $`z=\Delta+it`$ follows
by reweighting the row law. Along both expansions the real
basepoint at angular displacement zero has a positive value,
so the branches used in the equations are the required ones.

## Cancellation and final bound

The displacement term equals
$`nV\Delta t=\nu t(V/d)g'(x)+(nVt/d)E`$.
The covariance identity is exact because $`S(d-S)`$ is quadratic:

$$
\frac{V}{d}g'(x)-\frac ca
=\frac{\kappa_3}{d^2x(1-x)-V}
-\frac{V^2(1-2x)}{d x(1-x)[d^2x(1-x)-V]}.
$$

In particular the apparent contributions of order one in the two
angular arguments cancel. To bound the residual, use
$`d^2x(1-x)-V\ge d(d-1)x(1-x)\ge n^{1.97}/10`$
and $`V\le d x(1-x)`$.
The absolute value of the first term is at most $`10^{10}n^{-.47}`$.
The absolute value of the second is at most $`1/(d-1)`$.
Since $`\nu t<2`$ and $`nVt/d\le n^{.01}`$, the final deviation is
bounded by

$$
4n^{-.115}+10^{16}n^{-.47}+10^{17}n^{-.46}
+2\big(10^{10}n^{-.47}+1/(d-1)\big)<n^{-1/10}.
$$

The last inequality follows at $`u=10^6`$ by dividing by
$`n^{-1/10}`$ and bounding each resulting exponential, all of
which decrease with $`u`$.
