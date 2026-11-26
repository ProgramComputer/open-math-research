# Independent check of a bulk geometric-node reversal at critical aspect

Let $`d\to\infty`$, $`n/d^2\to\alpha\in(0,\infty)`$,
$`k/n\to x\in(0,1)`$, and $`k/n`$ stay a fixed positive distance below
$`r/d`$, with $`r<d`$. Let $`A_i`$ be the capped labeled-array coefficients,
$`P(q)=\sum_i A_iq^i`$, and $`t_k=\sqrt{A_{k-1}/A_{k+1}}`$.
The phase of the principal angular Gaussian contribution at
$`q=-t_k`$, less $`k\pi`$, tends to

$$
-\frac{\alpha\pi^3 x(1-x)(1-2x)}6.
$$

In particular, with the positive normalization specified below,
the signed polynomial tends to the cosine of this quantity. At a
zero of that cosine this computation makes no claim about the
eventual strict sign.

## Comparing the two geometric tilts

Write $`F_i=\binom ni^d`$ for the coefficients with no cap. For each
$`i=k\pm1`$, under the uniform measure on the uncapped arrays at
quota $`i`$, choose the columns independently as uniform $`i`$-subsets.
A given row then has distribution $`\mathrm{Bin}(d,i/n)`$.
The strict gap to $`r/d`$ and the binomial Chernoff bound give
$`1-A_i/F_i\le n e^{-c d}`$ for a constant $`c>0`$. No independence
of the row events is needed. Here $`n=O(d^2)`$, so polynomial factors
can be absorbed by reducing $`c`$.

Writing $`v=t_k^{1/d}`$, the corresponding uncapped tilt is

$$
v_0=\left(\frac{k(k+1)}{(n-k)(n-k+1)}\right)^{1/2}.
$$

Thus $`\log(v/v_0)=O(n e^{-c d}/d)`$. Put $`x_d=k/n`$ and
$`p_0=v_0/(1+v_0)`$. Since $`x_d`$ stays in a compact subset of
$`(0,1)`$, expansion of the logarithm in the preceding formula followed
by expansion of the logistic map gives

$$
p_0=x_d+\frac{1-2x_d}{2n}+O(n^{-2}).
$$

This uses the exact finite-size geometric node displacement to
first order. Its contribution to the principal phase is of order one.

## Comparing the angular terms at the actual tilt

At positive odds $`v`$, the tilted size $`S`$ is $`\mathrm{Bin}(d,p)`$,
$`p=v/(1+v)`$, conditioned on $`S\le r`$. The unconditional cap violation
probability is exponentially small in $`d`$, as $`p=x_d+o(1)`$.
Therefore $`\mu/d\to x`$, $`V/d\to x(1-x)`$, and
$`a\to x(1-x)`$ for its mean, variance and average transverse precision.
For variance comparison, multiplying the total variation error by
$`O(d^2)`$ still leaves an exponential error. At $`t=\pi/d`$ write
$`\phi(t)=\mathbb E e^{itS}`$ and
$`a(t)=\mathbb E[q_S e^{itS}]/\phi(t)`$, where
$`q_j=j(d-j)/[d(d-1)]`$. The unconditional characteristic is
bounded away from zero at this angle uniformly in the present
window. Its modulus is $`1-O(1/d)`$, for example by the centered
second-moment inequality. The complex expectations of the two
bounded test functions $`e^{itS}`$ and $`q_S e^{itS}`$ thus show that
$`\phi(t)`$ and $`a(t)`$ change by exponentially small absolute errors
on imposing the cap. The same conclusion holds on moving the
uncapped tilt from $`v`$ to $`v_0`$, since the derivative of each
expectation with respect to log odds is a covariance bounded by
$`O(d)`$ and $`\log(v/v_0)`$ is exponentially small. The uncapped
complex precision is bounded away from zero, since it converges to
$`x(1-x)`$. Both phase errors, even when multiplied by $`n`$ or $`d`$,
are therefore $`o(1)`$. These comparisons hold along the angular
path from $`0`$ to $`\pi/d`$, so they also justify the corresponding
continuous arguments.

At the actual tilt, all hypotheses of the existing critical-aspect
single-chart and global estimates hold. Indeed $`da\to\infty`$,
$`V\to\infty`$, $`r-\mu\asymp d`$, and $`n/d^2`$ belongs to a compact
positive interval. The single-chart bound applies at every near odd
angle using only these tilted quantities. For the principal chart,
$`b_t=(1+V)t^2=O(1/d)`$ and the error factor $`e_d=O(d^{-1/2})`$.
The magnitude of the complex determinant factor is bounded above
and below by constants because $`d b_t=O(1)`$. The complement,
remote regions, and all the other near labels have total
absolute integral $`o(|G_{\ast}|)`$. In the last region the estimates
sum a Gaussian lattice tail with parameter $`nV/d^2\asymp d`$,
independently of any phase alignment. Thus the requirement that
$`\Psi=k\pi`$ in the cited sign theorem enters only after these
estimates. In the present application the same phase-free bounds give

$$
\frac{P(-v^d)}{H(v)^n}=2\Re G_{\ast}+o(|G_{\ast}|),
$$

where $`H`$ is the capped row polynomial and $`G_{\ast}`$ is the principal
term of the actual capped integral. In particular $`2H(v)^n|G_{\ast}|`$
is the positive normalization of the polynomial used here.
The conjugate signs come from reflection on the determinant-minus-one
torus. [Critical-aspect angular estimates](https://github.com/ProgramComputer/open-math-research/blob/main/topics/balanced-arrays/critical-aspect/critical-aspect-angular-nodes.md)

## Exact binomial phase and its limit

For independent Bernoulli cells, conditioning on their count
does not change the definition of $`q_S`$. Direct differentiation
or binomial factorial moments give, at tilt $`v_0`$,

$$
\phi_0(t)=\left(\frac{1+v_0e^{it}}{1+v_0}\right)^d,qquad
a_0(t)=\frac{v_0e^{it}}{(1+v_0e^{it})^2}.
$$

Consequently the uncapped phase is

$$
(nd+d-1)\arg(1+v_0e^{it})-(d-1)t/2.
$$

Uniformly for $`p_0`$ in the compact density interval,
the analytic logarithm of $`1-p_0+p_0e^{it}`$ gives

$$
\arg(1+v_0e^{it})
=p_0t-\frac{p_0(1-p_0)(1-2p_0)}6 t^3+O(t^5).
$$

The fifth-order remainder follows by conjugation symmetry of the
analytic logarithm and a uniform analytic neighborhood of zero.
Since $`nd=O(d^3)`$ it contributes $`o(1)`$ at $`t=\pi/d`$.
The linear term less $`k\pi`$ is exactly

$$
\pi(np_0-k)+\pi\frac{d-1}{d}(p_0-1/2),
$$

which tends to zero by the expansion of $`p_0`$. Omitting either
the finite-size displacement of $`p_0`$ or the complex determinant
phase would in general lose this cancellation.
The cubic part tends to the displayed limit since
$`(nd+d-1)t^3\to\alpha\pi^3`$. The above exponentially small
cap and tilt changes preserve the limit for the actual polynomial.

At $`n=4d^2`$, $`k=d^2`$, and any $`\lceil d/2\rceil\le r<d`$,
the limiting phase displacement is $`-\pi^3/16`$, strictly between
$`-\pi`$ and $`-\pi/2`$. Its cosine is strictly negative.
Thus $`(-1)^kP(-t_k)<0`$ for all sufficiently large $`d`$,
uniformly over those proper caps. The strict gap estimates are
uniform in $`r`$, and the angular estimates have the same compact
aspect and interior hypotheses across all sequences of these caps.
The existing critical-aspect root theorem still gives simple
negative zeros in this example. This is a failure of the
geometric-node sign test. [Critical-aspect theorem](https://github.com/ProgramComputer/open-math-research/tree/main/topics/balanced-arrays/critical-aspect)

The closest known project precedents are the fixed-dimension bulk
geometric-center failures and the uncapped hyper-Bessel limit.
The former takes fixed $`d`$ and the latter uses a different
lower-end scaling. This calculation uses bulk density, proper caps
and $`n/d^2\to\alpha`$. I make no priority claim.
[Fixed-d bulk study](https://github.com/ProgramComputer/open-math-research/blob/8a0a986e6baeed69b30de189e75c02fd2c8cb955/topics/balanced-arrays/geometric-centers/bulk-center-density.md)
· [Uncapped hyper-Bessel study](https://github.com/ProgramComputer/open-math-research/blob/8a0a986e6baeed69b30de189e75c02fd2c8cb955/topics/balanced-arrays/geometric-centers/hyperbessel-centers.md)
