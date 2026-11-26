# Principal angular charts at the original logarithmic height

Let $`u=\log n\ge10^6`$, $`n^{.99}\le d\le n`$, and let $`S`$ have
the actual tilted capped-binomial law. Write $`a_s=s(d-s)/(d(d-1))`$,
$`a=\mathbb E a_S`$, $`A=na`$, $`V=\mathrm{Var}(S)`$, and
$`\phi(t)=\mathbb E e^{itS}`$. Assume $`A/d\ge u/111`$.
The geometric-tilt transfer supplies this lower bound in the low-curvature
case. The ordinary variance comparison gives $`V\le da`$.
Let $`t=\pi/d`$ or $`-\pi/d`$, $`\nu=(d-1)/2`$, and set

$$
a(t)=\frac{\mathbb E[a_S e^{itS}]}{\phi(t)},\qquad
G_t=\frac{(2\pi A)^{-\nu}}{\sqrt d}\thinspace{}
       \phi(t)^n\left(\frac{a}{a(t)}\right)^\nu .
$$

On the transverse ball $`\mathcal C`$ of zero-sum vectors of Euclidean
norm at most $`b=2/5`$ about that common angle, let $`I_t`$ be the
normalized Haar integral of the $`n`$th power of the row factor.
Then

$$
|I_t-G_t|<.02\thinspace{}|G_t|.
$$

This supplies the principal-chart input for the larger-radius
suppression argument in
[Global integral estimates](angular-mass-dominance.md#larger-radius-global-version-at-the-original-row-cutoff).
That argument also requires the lower bound $`nV/d^2\ge u/400`$.
Together the three global terms and the two local errors cost
less than $`.07|G_t|`$.

## Precision and row-size mixing

Let $`Q_j=\sum_i y_i^j`$ and $`M=\max_i|y_i|`$. Put
$`\varepsilon=n^{-2/5}`$ and let $`\mathcal I`$ be the part of
$`\mathcal C`$ with $`M\le\varepsilon`$. Write
$`\gamma_s=a_s(d-2s)/(d-2)`$, and use
$`\mathbb E_t g=\mathbb E[g e^{itS}]/\phi(t)`$ and
$`\gamma(t)=\mathbb E_t\gamma_S`$. The centered second-moment
inequality gives $`|\phi(t)|\ge1-Vt^2/2>.999`$ because
$`Vt^2\le10 a/d`$ and $`d`$ is large. For a real function $`g`$ of
$`S`$ with Lipschitz constant $`L_g`$, the independent-copy covariance
identity gives

$$
|\mathbb E_t g-\mathbb E g|\le L_g V |t|/|\phi(t)|,\qquad
\mathbb E|g-\mathbb E_tg|^2
\le L_g^2 V\left(1+Vt^2/|\phi(t)|^2\right).
$$

The second bound uses the exact decomposition of the squared
distance from a complex constant into the ordinary variance
and the squared distance of the constants. Direct differentiation
gives $`L_{a_s}\le1/(d-1)`$ and $`L_{\gamma_s}\le3/d`$ on $`[0,d]`$.
Also $`|\gamma_s|\le a_s`$ at the integer sizes. It follows that

$$
|a(t)-a|\le 3a|t|,\qquad |\gamma(t)|\le1.01a,\qquad
|\Im\gamma(t)|\le3.01a|t|.
$$

Let $`A_t=n\Re a(t)`$. Then $`A_t\ge.999 A`$ and
$`A_t/d\ge u/112`$. The modulus-normalized real Gaussian integral
has scale

$$
J_t=\frac{(2\pi A_t)^{-\nu}}{\sqrt d}|\phi(t)|^n.
$$

The full complex quadratic integral equals $`G_t`$, since
$`\Re a(t)>0`$. The ratio of real to complex scales satisfies

$$
\log(J_t/|G_t|)
=\frac{\nu}{2}\log\left(1+\frac{(\Im a(t))^2}{(\Re a(t))^2}\right)
<3dt^2\le30/d ,
$$

so $`J_t/|G_t|<1.001`$ at the stated cutoff.

On $`\mathcal I`$, the fixed-size row expansion gives the logarithm
of its transverse factor as $`L_s+E_s`$, where
$`L_s=-a_sQ_2/2-i\gamma_s Q_3/6`$ and

$$
|E_s|\le a_s((7/24)Q_4+8Q_2M^3).
$$

The quartic bound here uses $`|A_{4,s}|\le a_s`$,
$`|B_{4,s}|\le2a_s/d`$ and $`Q_2^2/d\le Q_4`$.
Put $`D_s=L_s-\mathbb E_t L_S`$, so $`\mathbb E_t D_S=0`$.
The preceding variance bounds give, under the ordinary size law,

$$
\Vert a_S-a(t)\Vert _2\le1.01\sqrt V/d,\qquad
\Vert \gamma_S-\gamma(t)\Vert _2\le3.01\sqrt V/d.
$$

By $`|Q_3|\le M Q_2`$, these imply
$`\|D_S\|_2\le .52 Q_2\sqrt V/d`$ on $`\mathcal I`$.
In particular $`\mathbb E|D_S|^2\le.28\,aQ_4`$.
The uniform bound $`a_s\le.26`$, the bound $`|\phi(t)|>.999`$,
and $`Q_2\le.16`$, $`M\le\varepsilon<.001`$ give
$`|D_s|+|E_s|<.06`$ for every size. The integral remainder of
the exponential therefore gives

$$
|e^{D_s+E_s}-1-D_s|\le1.1|E_s|+.55|D_s|^2.
$$

With $`z=\mathbb E_t e^{D_S+E_S}-1`$, averaging and using the
vanished linear term yield $`|z|\le .5aQ_4+9aQ_2 M^3<.01`$:
the coefficient of $`aQ_4`$ before rounding is at most
$`(1.1(7/24)+.55(.28))/.999<.5`$.
Thus the summed row factor on $`\mathcal I`$ has the logarithm

$$
\log(R(t,y)/\phi(t))=-a(t)Q_2/2-i\gamma(t)Q_3/6+E,\qquad
|E|\le .52aQ_4+10aQ_2M^3 .
$$

Here $`\log(1+z)`$ is its local analytic branch and costs at
most $`|z|/(1-|z|)`$. [Fixed-size expansion](direct-row-expansion.md)

## A Gaussian fourth-power bound on the larger ball

For any precision $`B\ge A/2`$, let $`Y_j=Z_j-\bar Z`$ where the
$`Z_j`$ are independent $`N(0,1/B)`$ random variables. Then

$$
\mathbb E[\mathbf1_{\mathcal C}\exp(1.68 B Q_4(Y))]<4 .
$$

Insert the independent event $`|\bar Z|\le2/\sqrt{dB}`$ at
cost at most $`4/3`$ by Chebyshev. On its intersection with the
ball, $`|Z_j|\le.401`$. The weighted fourth-power inequality

$$
|Z_j-\bar Z|^4\le(9/8)^3|Z_j|^4+9^3|\bar Z|^4
$$

follows by convexity of the fourth power. Consequently the
deterministic offset in the exponent is less than
$`20000/(dB)<.01`$. The single-coordinate exponent is bounded
by $`2.4 B Z_j^4\le (2/5)B Z_j^2`$ on the truncation.
For a standard normal $`X`$,
$`\mathbb E[X^4e^{(2/5)X^2}]=3\cdot5^{5/2}<170`$.
The bound $`e^w-1\le we^w`$ and independence therefore give
$`(4/3)\exp(.01+408d/B)<4`$, since $`d/B\le222/u`$.

## Inside the small maximum window

Under the normalized zero-sum Gaussian of precision $`A_t`$ put
$`H=-in\gamma(t)Q_3/6+nE`$ on $`\mathcal I`$. The cubic moment has
$`\|Q_3\|_2\le\sqrt{6d}/A_t^{3/2}`$ by the zero-sum Wick identity.
The eighth normal moment and Minkowski give
$`\|Q_4\|_2\le\sqrt{105}\,d/A_t^2`$.
Also $`\|A_tQ_2\|_2\le d`$ from the chi-square distribution with
$`d-1`$ degrees of freedom. Thus the inner correction satisfies

$$
\Vert \mathbf1_{\mathcal I}H\Vert _2
\le .42\sqrt{d/A_t}+5.4d/A_t+11d\varepsilon^3<.006 .
$$

In the last comparison, $`\sqrt{d/A_t}\le.011`$,
$`d/A_t\le.000112`$ and $`d\varepsilon^3\le n^{-1/5}`$.
On $`\mathcal I`$ the possible positive real part of the cubic
is at most $`.51 A |t|\varepsilon Q_2`$.
Together with $`10A Q_2\varepsilon^3`$ it is less than $`.001`$,
because $`A|t|\le4n^{.01}`$ and $`Q_2\le.16`$.
It follows that $`(\Re H)_+\le .53 A_t Q_4+.001`$ on
$`\mathcal I`$. The larger-ball quartic bound above gives
$`\mathbb E[\mathbf1_{\mathcal I} e^{2(\Re H)_+}]<5`$.
By Cauchy–Schwarz and $`|e^H-1|\le |H|e^{(\Re H)_+}`$,
the integrated replacement error on $`\mathcal I`$ is
less than $`.006\sqrt5\,J_t<.014J_t`$.

## Restoring the two tails

The real Gaussian at precision $`A_t`$ has probability at most
$`2d e^{-A_t\varepsilon^2/2}`$ for $`M>\varepsilon`$.
For $`Q_2>b^2`$, exponential Markov with the chi-square parameter
$`1/4`$ bounds its probability by
$`2^{(d-1)/2}e^{-A_t b^2/4}\le e^{-300d}`$.
Thus extending the full complex quadratic integral from
$`\mathcal I`$ to the whole subspace costs less than $`.001J_t`$
in modulus.

For the actual integral on $`\mathcal C\setminus\mathcal I`$, use
the matched envelope from the global proof, with
$`B_y=Q_2/2-1.26 Q_4`$. It gives

$$
|R(t,y)|^n\le|\phi(t)|^n
\exp\left[-A Q_2/2+1.26A Q_4
 +\frac{nV B_y^2}{(d-1)^2}+\frac{2nV|t|Q_2}{d}\right].
$$

Since $`B_y\le .08`$, $`Q_2\le .16`$ and $`|t|=\pi/d`$,
the sum of the last two terms is at most $`2nV/d^2\le2 A/d`$.
Apply Hölder with exponents $`4/3,4`$ under the precision-$`A`$
Gaussian. The larger-ball quartic expectation uses coefficient
$`(4/3)(1.26)=1.68`$, and the other factor is the fourth root of
the probability of $`M>\varepsilon`$. In units $`|G_t|`$, the outer
actual contribution is at most

$$
4e^2\exp(2A/d)(2d)^{1/4}e^{-A\varepsilon^2/8}<.001 .
$$

Here $`(2\pi A)^{-\nu}|\phi(t)|^n/\sqrt d\le e^2|G_t|`$
as in the global calculation. To check the exponents,
$`d\varepsilon^2\ge n^{.19}>32`$ allows the positive term
$`2A/d`$ to use at most half of the negative exponent.
The remaining $`A\varepsilon^2/16`$ exceeds $`100u`$
since $`A/d\ge u/111`$. These inequalities also verify the
small maximum tail for $`A_t\ge.999 A`$.

Combining the inner error and the two tails gives
$`(.014+.001)J_t+.001|G_t|<.02|G_t|`$, as claimed.
