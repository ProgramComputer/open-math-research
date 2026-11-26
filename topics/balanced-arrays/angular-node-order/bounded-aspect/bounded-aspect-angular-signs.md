# Exact angular sign at central quotas of bounded rectangular aspect

Let $n,d\to\infty$, $n\ge d$, $d/n\to s_0>0$, and
$1\le r<d$. Let $k$ be an internal quota and suppose
$x=k/n\to x_0\in(0,1)$. Let $w_{\ast}$ be the exact ordered angular
tilt, so $\Psi(w_{\ast})=k\pi$. Then along every such sequence,

$$
(-1)^k P_n(-w_{\ast}^d)>0
$$

eventually. The cap can enter or cross the transition region as the
parameters vary, including fixed deficits from saturation. The result
is sequential and gives no explicit height cutoff.

## Inputs and notation

Put $s=d/n$, $\theta=\pi/d$, $\nu=(d-1)/2$,
$g(x)=\log(x(1-x))$, and $\mu=dx$.
Write $S$ for the capped binomial row tilted to mean $\mu$,
$V=\mathrm{Var}(S)$, $q_j=j(d-j)/(d(d-1))$, and $a=\mathbb E q_S$.
Let $H$ be the capped row polynomial and let
$\mathcal U_j=[z^{dj}]H(z)^n$ be the scalar coefficients. Write
$Q_j=a_j/\mathcal U_j$, where $a_j$ is the balanced coefficient.

Use the finite strict-ordering theorem for the tilted angular
phase. The explicit adjacent comparison gives, for any fixed integer
$j$ with all intermediate quotas feasible,

$$
\log(Q_{k+j}/Q_k)=-\nu[g(x+j/n)-g(x)]+o(1).
$$

We use a qualitative compact-density extension of the published
comparison, proved in the next section, since its explicit statement
uses the density interval $[s/3,1-s/3]$. The balance log ratio is bounded
for every fixed offset.
[Angular ordering](https://github.com/ProgramComputer/open-math-research/blob/8d9a0cfdd12bf23086bcc2db05691310b9d3a126/topics/balanced-arrays/angular-node-order/README.md)
· [Adjacent coefficient comparison](https://github.com/ProgramComputer/open-math-research/blob/6a91a65e940e8aa9adadb3be9fe344266eb22d59/topics/balanced-arrays/effective-sublinear/direct-comparison.md)

We also use the capped binomial variance upper bound $V\le d x(1-x)$,
the lower bound $V\ge dx(r/d-x)/(r/d)$, and the scalar local
limit and moment bounds. At means where $\sigma=\sqrt V\to\infty$,
the standard deviation is locally $10^9$-Lipschitz as a function
of the mean and $\mathbb E|S-\mu|^3\le10^9\sigma^3$.
A finite mean displacement therefore changes $V$ by a relative
$o(1)$, as long as the intervening means are in the support
interior. A first-exit argument applies the Lipschitz estimate
up to any possible first point with $\sigma=10^4$, excluding
that possibility within a fixed mean displacement.
[Scalar estimates](https://github.com/ProgramComputer/open-math-research/blob/7210ef194132ebad5d0e2ebda61c2aadccc973a4/topics/balanced-arrays/adjacent-quotas/scalar.md)
· [Carried-load variance lower bound](https://github.com/ProgramComputer/open-math-research/blob/27e3e70d6603e8a395c5fdb7ff944922bce83380/topics/balanced-arrays/engset-curvature/carried-load.md)

Finally normalized log-concavity gives outward decreasing term
ratios for the balanced coefficient series at every positive
radius. We use it only after bounding ratios in a local window.
[Normalized log-concavity](https://github.com/ProgramComputer/open-math-research/blob/78e9ef2c0c0b7a5daed126efbe12a46d030d8200/topics/balanced-arrays/orientation-normalization.md)

## Qualitative comparison on every fixed interior density interval

Take $x$ in a fixed compact subinterval of $(0,1)$ and $d\asymp n$.
We explain the changes to the published direct comparison. The constants
in this section may depend on these two compact intervals. Regular row
profiles with $|p_i-x|\le\eta=n^{-1/4}$ have $v_i=p_i(1-p_i)$
uniformly bounded below and precision $\lambda\asymp n$.
The Bessel off-chart proof only needs $v_i\ge1/T$, $d\ge n/T$,
$n/(2T^2)\ge10$, $A-n/d\ge n/(2T)$, and
$\log(2\pi n)\le n/(4T^2)$, where $A=\sum_i v_i$.
All hold with a fixed sufficiently large $T$ as $n\to\infty$.
Its relative error is still negligible at diameter $n^{-2/5}$.
[Off-chart estimate](https://github.com/ProgramComputer/open-math-research/blob/6a91a65e940e8aa9adadb3be9fe344266eb22d59/topics/balanced-arrays/effective-sublinear/direct-row-tail.md)

The fixed-profile calculation from the direct comparison now has
$\lambda\ge c n$ for some $c>0$ in place of $\lambda\ge d/5$.
The determinant formula, summed row error $\lVert R\rVert_2=O(n^{-1/5})$,
real bound $|\Re R|<1$, and fourth-power exponential truncation
are unchanged except that the exponential expectation is bounded by
a constant depending on $c$. The quartic mean $m$ stays bounded
and its fluctuations are $O(\sqrt d/\lambda)=o(1)$.
Thus the normalized fixed-profile probability is
$e^m\mathbb E\cos(\xi C_d)+o(1)$ uniformly over regular profiles,
where $\xi=-\Gamma\sqrt d/(6\lambda^{3/2})$ is bounded and
$C_d=d^{-1/2}\sum_j(Z_j-\bar Z)^3$ for independent standard
Gaussians. The former simple lower bound for the cosine need not
work. Instead expand

$$
C_d=d^{-1/2}\sum_j(Z_j^3-3Z_j)
+d^{-1/2}\left[-3\bar Z\sum_j(Z_j^2-1)+2d\bar Z^3\right].
$$

The bracket has bounded $L^2$ norm by Cauchy–Schwarz and the Gaussian
fourth moments of $\bar Z$ and of $\sum_j(Z_j^2-1)$, so the
second term tends to zero in $L^2$. The first tends to a centered
normal of variance six by the iid central limit theorem. The
expectations $\mathbb E\cos(\xi C_d)$ therefore tend uniformly
on compact $\xi$ intervals to $\exp(-3\xi^2)$: equicontinuity
follows from the bounded first absolute moments of $C_d$.
This gives a strictly positive constant lower bound for the
regular fixed-profile correction.

For the monotone coupling of adjacent scalar profiles, the sum of
the absolute changes of the cell probabilities is one. The same
polynomial derivative bounds used in the direct comparison show
that $\lambda,\Gamma,A_{\ast},dB_{\ast}$ change by bounded amounts.
At $\lambda\asymp n$ the quartic mean and the coefficient $\xi$
therefore change by $O(1/n)$. The cosine is Lipschitz in $\xi$
with a bounded constant, so the difference of the logs of the
corrections is $o(1)$ uniformly on regular coupled pairs after
including the chart errors. The determinant correction also has
log variation $O(\eta)$ by $|B'-B|\le4\eta$ and bounded
$1/v$, with $B=\sum(p_i-x)^2$, $v=x(1-x)$.

Finally the regular fixed-profile factors divided by
$\sqrt d(2\pi n v)^{-\nu}$ are bounded below by a positive
constant and bounded above by $C e^{CB}$. The same integrated
scalar Hoeffding estimate used in the direct comparison bounds
the regular weighted second moment by $C(nd+1)e^{C n/d}$.
The two-row and scalar irregularity probabilities are
$O(n^3)e^{-c d\eta^2}$ for an absolute $c>0$.
Hence discarding pairs for which either profile is irregular
loses an $o(1)$ fraction of the weighted expectations, exactly
by the actual-law irregularity bound for its own marginal and
Cauchy–Schwarz for the other marginal. Integrating the regular
pair comparison gives the desired neighboring log ratio with
error $o(1)$. Telescoping works for every fixed offset.

## Proportional row variance

By a subsequence take $V/d\to v_0>0$. Let $w_0$ be the positive
tilt at mean $\mu$ and set $t=\theta$. At test tilts
$w_0e^{y/d}$ with bounded real $y$, use $z=y/d+it$ in the
centered row transform $\mathbb E e^{z(S-\mu)}$. Since
$|z|=O(1/d)$, $|S-\mu|\le d$, and
$\mathbb E|S-\mu|^3=O(d^{3/2})$, its logarithm is
$Vz^2/2+O(d^{-3/2})$ uniformly for bounded $y$.

For the precision use $\mathbb E[q_S e^{z(S-\mu)}]/ \mathbb E e^{z(S-\mu)}$. Writing $c=\mathrm{Cov}(q_S,S)$,
its logarithm is $\log a+(c/a)z+O(d^{-3/2})$.
Indeed $q_j$ is $2/d$-Lipschitz, so the second weighted remainder
is bounded by a constant times
$|z|^2(\mathbb E|S-\mu|^3+V^{3/2})/d$.
Also $a\ge x(1-x)$ by the variance upper bound. These two expansions
fix the branches by continuity from the real axis and give

$$
\Psi(w_0e^{y/d})-k\pi
=\frac{\pi n V}{d^2}y-\nu t\frac ca+o(1).
$$

The first coefficient tends to $\pi v_0/s_0>0$, and the determinant
term is bounded. Bracketing by two fixed values of $y$ and then
applying the expansion at the actual tilt gives

$$
d\log(w_{\ast}/w_0)=\frac{d\nu}{n V}\frac ca+o(1).
$$

The covariance is an explicit quadratic computation:

$$
\frac ca
=\frac{d(1-2x)V-\mathbb E(S-\mu)^3}{d^2x(1-x)-V}
=\frac{V}{d}g'(x)+O(d^{-1/2}).
$$

Consequently $d\log(w_{\ast}/w_0)=\nu g'(x)/n+o(1)$.
This is the cancellation against the coefficient balance drift.

The scalar entropy at row mean $m$ is
$f(m)=\log H(w(m))-m\log w(m)$, with
$f'(m)=-\log w(m)$ and $f''(m)=-1/V(m)$.
At every fixed offset $j$, the mean is $\mu+sj$, and $V(m)/V\to1$
throughout the intervening interval. The scalar local limit
prefactors at the two tilts have ratio $1+o(1)$.
All fixed offsets are feasible eventually: otherwise the total
deficit divided by $n$ would be bounded, in which case the bounded
deficit tilt argument below gives bounded row variance, contrary
to $V/d\to v_0>0$. The lower endpoint is remote since $k/n$ is central.
Combining the entropy Taylor integral, scalar prefactors, and balance
comparison gives, uniformly at each fixed $j$,

$$
\log\frac{a_{k+j}w_{\ast}^{d(k+j)}}{a_kw_{\ast}^{dk}}
= -\frac{n s^2}{2V}j^2+o(1).
$$

Indeed the linear scalar drift is $dj\log(w_{\ast}/w_0)$ and the
linear balance drift is $-\nu g'(x)j/n$. Thus the signed
normalized series tends to
$\sum_{j\in\mathbb Z}(-1)^j e^{-s_0 j^2/(2v_0)}>0$,
by the Jacobi product. To pass to the infinite sum, the first
outward ratios converge to $e^{-s_0/(2v_0)}<1$ and all subsequent
outward ratios are smaller by log-concavity.

## Subproportional row variance and diverging deficit

Take $V/d\to0$ and $h=nr/d-k\to\infty$. The carried-load bound
gives $V\to\infty$ since $r-dx=sh$. For means a fixed distance
from $\mu$, the centered third-moment bound gives
$n\arg(H(we^{it})/H(w))=nmt+o(1)$ at tilt mean $m$.
Here the error is $O(n V^{3/2}/d^3)=o(1)$.
The precision argument contributes $O(V/d)=o(1)$, by
$|\mathrm{Cov}(q_S,e^{itS})|\le2V|t|/d$ and $a\asymp1$.
Both bounds are uniform on a fixed mean interval about $\mu$.
Bracketing phases at mean $\mu\pm\epsilon$ for arbitrary fixed
$\epsilon>0$ yields $m_{\ast}=\mathbb E_{w_{\ast}}S=\mu+o(1)$.
Therefore
$\log(w_{\ast}/w_0)=o(1/V)$ by integrating $1/V(m)$ between these means.
For $j=\pm1$, the same scalar entropy Taylor integral now gives

$$
\log\frac{\mathcal U_{k+j}w_{\ast}^{d(k+j)}}{\mathcal U_kw_{\ast}^{dk}}
=-\frac{n s^2}{2V}(1+o(1))+O(1)\longrightarrow-\infty .
$$

The linear drift is $o(n/V)$, and the scalar local limit
prefactor ratios are bounded. The balance-factor ratios are also
bounded. Thus both actual adjacent term ratios tend to zero, and
pairing the outward alternating tails gives strict positivity.

## Bounded deficit

Pass to a subsequence with $h\to h_0\ge1$ and $r/d\to x_0$.
For a fixed odds $w$ close to
$w_\infty=x_0(1+1/(s_0 h_0))/(1-x_0)$, the deficit $J=r-S$ has
successive ratios bounded by a constant below one and converging
for every fixed deficit index to
$x_0/[(1-x_0)w]$. This is because the ratio of the binomial
coefficients at $r-\ell-1,r-\ell$ is
$(r-\ell)/(d-r+\ell+1)$. Thus the deficit law converges
to a geometric law and has a uniform exponential moment.
Its limiting mean at $w_\infty$ is $s_0 h_0$.
Bracketing the mean with fixed odds either side shows
$w_0\to w_\infty$, and in particular proves the bounded variance
assertion used above for bounded deficits.

At those same bracketing odds the phase is $nmt+O(1/d)$ at
row mean $m$. Indeed the third centered moment is bounded,
and the covariance precision estimate is now $O(1/d)$ after
multiplication by $\nu$. Since $n/d$ stays bounded away from zero,
the phase brackets $k\pi$ at any two sufficiently close fixed
odds to either side of $w_\infty$. Hence $w_{\ast}\to w_\infty$ as well.
The scalar probability at quota $k$ under tilt $w_0$ is at least
$1/(nd+1)$ by the integer-mean atom bound for log-concave
laws. Moving to the odds $w_{\ast}$ changes its log probability by
$o(n)$, as follows from the exponential-family likelihood
ratio and the bounded first deficit moments between the two odds.
Thus the center atom under $w_{\ast}$ is $e^{-o(n)}$.

For each adjacent quota, the required average deficit differs
from the actual tilted mean by at least $s_0/2$ eventually.
The uniform exponential moment gives the scalar Chernoff bounds
$e^{-c_0 n}$ with $c_0>0$: center each deficit summand, use a
uniform quadratic bound for its log moment generating function
in a fixed neighborhood of zero, and choose a small fixed tilt
in the appropriate direction. This includes a saturated neighbor
with zero deficit. Again the balance-factor ratios are bounded.
Both actual adjacent term ratios vanish, so log-concavity and
alternating pairing finish the sign argument.

Every potential sequence of failures admits a subsequence in one
of the three cases, giving the claimed bounded-aspect central
result. This rules out a limiting reversal at central density
and bounded rectangular aspect, even when $n/d$ exceeds the
binomial separation threshold. It leaves possible failures at
finite heights, at densities tending to an endpoint, or at
unbounded rectangular aspect.
