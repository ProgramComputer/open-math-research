# Quantitative global dominance of the two principal odd angles

Let $`u=\log n`$, $`n^{.99}\le d\le n`$, and let $`S`$ have the tilted
capped-binomial law in the angular argument. Put
$`a_s=s(d-s)/(d(d-1))`$, $`a=\mathbb E a_S`$, $`V=\mathrm{Var}(S)`$,
$`A=na`$, $`L=nV/d^2`$, $`\phi(t)=\mathbb E e^{itS}`$,
$`t_{\ast}=\pi/d`$, and $`\nu=(d-1)/2`$. Assume
$`A/d,L\ge u/400`$.
Write $`R(\theta)=\mathbb E e^{i\sum_{j\in I_S}\theta_j}`$, where
$`I_S`$ is the uniform row subset given its size. Use normalized Haar
measure on $`\sum_j\theta_j=\pi`$ modulo $`2\pi`$ and the notation

$$
I_0=\frac{(2\pi A)^{-\nu}}{\sqrt d},\qquad
G_{\ast}=I_0\phi(t_{\ast})^n\left(\frac a{a(t_{\ast})}\right)^\nu,\qquad
a(t)=\frac{\mathbb E[a_S e^{itS}]}{\phi(t)} .
$$

At $`u\ge10^{60}`$, use disjoint transverse balls of radius
$`b=10^{-3}`$ around the common angles $`t=j\pi/d`$ of odd label.
The nonprincipal near charts, remote charts, and the complement of
the balls each contribute less than $`|G_{\ast}|/100`$. The estimate
on a single principal chart in
[the principal-chart estimate](angular-principal-chart.md)
then gives total error less than $`|G_{\ast}|/4`$ after keeping the
principal conjugate pair. The comparison uses the magnitude of
one principal term, so it is valid even when their real parts cancel.
At a phase node the two principal terms have the same real sign.

The global bounds below quantify the two-saddle-dominance part of
the earlier asymptotic argument. The last section gives a
larger-radius alternative at $`u\ge10^6`$.
[Earlier transverse and global argument](https://github.com/ProgramComputer/open-math-research/blob/main/topics/balanced-arrays/eventual-all/analytic-angular-signs.md)

## Preliminary bounds and the principal scale

The truncated-binomial variance bound gives
$`V\le\mu(1-\mu/d)`$ at all tilts, with $`\mu=\mathbb ES`$.
For example, its ratio to the binomial mass of mean $`\mu`$ has
interval superlevel sets. Subtracting a chord through the two
sign changes of the mass difference, using equality of mass
and mean, proves convex-order domination by that binomial.
In particular $`V\le da`$, since
$`d(d-1)a=\mu(d-\mu)-V`$. We will use

$$
a\le.26,\qquad a\ge n^{-.01},\qquad da\ge n^{.98},\qquad
da^2\ge n^{.97},\qquad V\ge n^{.98}.
$$

These hold for $`u\ge10^6`$ by $`L\ge u/400`$, $`d\ge n^{.99}`$,
and $`a\ge V/d`$. Write $`\phi_{\ast}=\phi(t_{\ast})`$.
The centered second-moment inequality gives
$`|\phi_{\ast}|\ge1-Vt_{\ast}^2/2`$, and $`Vt_{\ast}^2\le10a/d<1`$.
Thus $`\log(1/|\phi_{\ast}|)\le Vt_{\ast}^2`$. Since
$`|a(t_{\ast})|\le a/|\phi_{\ast}|`$,

$$
|G_{\ast}|\ge I_0|\phi_{\ast}|^{n+\nu}\ge I_0e^{-15A/d},
\qquad
|G_{\ast}|\ge e^{-2}I_0|\phi_{\ast}|^n .
$$

The second bound uses $`\nu Vt_{\ast}^2\le5a\le1.3`$.
The principal complex precision is nonzero by the near-chart
estimates, or directly using the Lipschitz bound on $`a_s`$
and the independent-copy covariance identity.

## A pointwise envelope on the full torus

Set $`z_j=e^{i\theta_j}`$, $`R_0=|\sum_j z_j|`$,
$`\bar z=d^{-1}\sum_j z_j`$, and $`D=\sum_j|z_j-\bar z|^2`$.
Then $`D=(d-R_0)(1+R_0/d)\le d`$.
For a fixed size $`s`$ let $`w_s=s(d-s)/d^2`$ and $`f_s`$ be its
characteristic function. Conditioning independent Bernoulli
cells at their mean atom $`b_s`$, then integrating the row angle
in absolute value, gives

$$
|f_s|\le b_s^{-1}e^{-w_s(d-R_0)}J(w_sR_0),
\qquad J(x)=e^{-x}I_{\negthinspace{}B}(x),
$$

where $`I_{\!B}`$ denotes the order-zero modified Bessel function.
On $`\mu/2\le s`$ and $`(d-\mu)/2\le d-s`$, we have
$`w_s\ge\mu(d-\mu)/(4d^2)\ge a/5`$.
For $`R_0\ge d/2`$ use the Bessel upper bound
$`J(x)\le e^{1/(2x)}(2\pi x)^{-1/2}`$ for $`x\ge10`$ and
$`b_s\ge (2\pi d w_s)^{-1/2}e^{-1/(12d w_s)}`$ from Stirling.
Then

$$
\log |f_s|\le -w_s(d-R_0)+\frac{d-R_0}{d}
       +\frac{13}{12d w_s}
\le -.09aD+\frac6{da}.
$$

Here $`d w_s\ge da/5\gg100`$, and
$`D\le2(d-R_0)`$. On $`R_0<d/2`$ use $`J\le1`$. The
Stirling prefactor costs at most
$`\tfrac12\log(2\pi d w_s)+1/(12d w_s)\le u`$,
which is smaller than $`w_s(d-R_0)/10`$ because
$`w_s(d-R_0)/10\ge da/100>u`$. This gives
$`\log |f_s|\le-.09aD`$ in this case.
[Bessel and row-atom inequalities](direct-row-tail.md)

The probability of either excluded size event is at most
$`2e^{-.14da}`$. To see this, for the tilted mean $`m(\eta)`$
of $`S`$ use $`m'(\eta)\le m(\eta)`$ at every tilt.
Integrating $`m(-t)\ge\mu e^{-t}`$ shows
$`\log\mathbb E e^{-tS}\le-\mu(1-e^{-t})`$.
Chernoff at $`t=\log2`$ gives the lower-tail bound
$`e^{-\mu(1-\log2)/2}`$, and the same argument applies to
$`d-S`$. Since $`\min(\mu,d-\mu)\ge(d-1)a`$ and $`\log2<.7`$,
this gives the displayed excluded probability. Average the two
good-row bounds and use $`D\le d`$. For $`z=da\ge267`$,
$`2e^{-.05z}\le6/z`$ by the quadratic exponential bound.
Consequently on the entire torus, for $`u\ge10^6`$,

$$
|R|\le e^{-.09aD}\big(e^{6/(da)}+2e^{-.05da}\big)
\le \exp\left(\frac{12}{da}-.09aD\right).
$$

## Complement of the transverse balls

For $`b\le2/5`$, the balls $`\theta=t\mathbf1+y`$,
$`\sum_jy_j=0`$, $`\|y\|_2\le b`$ at the odd labels are disjoint.
If two lifts agreed modulo $`2\pi`$, their coordinatewise differences
would be congruent to one common real number. Those differences
are in an interval of length $`4b<2\pi`$, so they are equal, and
their zero sum then forces the labels to agree.

On the complement, $`D\ge b^2/3`$. Indeed if $`D<b^2/3`$,
then $`R_0/d>.99`$. Taking principal relative angles $`x_j`$ to
$`\arg\bar z`$ gives $\sum_j x_j^2\le
(\pi^2/4)2D/(1+R_0/d)<3D$. Subtract their ordinary mean to get
a zero-sum lift $`y`$ of norm below $`b`$. The common angle has an odd
label because the original angle sum is $`\pi`$ modulo $`2\pi`$.
This identifies a ball containing the point.

Partition the complement over indices $`i`$ minimizing
$`|z_i-\bar z|`$. On each part
$`\sum_j|z_j-z_i|^2\le2D`$, so in principal relative angles
$`u_j=\arg(z_j/z_i)`$ we have $`\sum_{j\ne i}u_j^2\le5D`$.
For a fixed anchor the relative-angle map pushes Haar to
full normalized Haar in $`d-1`$ coordinates, since it is a
surjective homomorphism up to translation. Indeed for any
relative angles the equation for $`d\theta_i`$ on the circle
has a solution. Split the penalty $`.09AD`$ into two halves.
The first gives $`.015Ab^2`$. The second is at least
$`.009 A\sum_{j\ne i}u_j^2`$. Integrating the resulting Gaussian
on each part, and extending those real integrals to the full
line, gives in the units $`I_0`$

$$
I_0^{-1}\int_{\text{outside the balls}} |R|^n
\le d^{3/2}(1/.018)^\nu
       \exp\left(\frac{12n}{da}-.015 A b^2\right).
$$

The power of $`d`$ includes the sum over anchors and the
Haar correction of $`I_0`$. Dividing by $`|G_{\ast}|/I_0`$ gives a
logarithmic bound $`12n/(da)-.015Ab^2+3d+15A/d`$,
since $`\tfrac32\log d+\nu\log(1/.018)\le3d`$.
When $`b=10^{-3}`$ and $`u\ge10^{60}`$ this is at most
$`-10^{-8}A`$. In fact the positive terms divided by $`A`$
are respectively $`12/(da^2)`$, at most $`1200/u`$, and $`15/d`$.
At $`b=2/5`$ the same expression is at most $`-.001A`$ already
for $`u\ge10^6`$.

## Remote odd labels

Use near labels $`|t|\sqrt V\le10^{-3}`$ and remote labels
in the complementary part of the circular interval $`[-\pi,\pi]`$.
The numerical log-concave Fourier estimate gives
$`|\phi(t)|\le\exp[-10^{-18}\min(Vt^2,1)]`$ because
$`\sqrt V\ge10^4`$. In particular remote labels have
$`|\phi(t)|\le e^{-10^{-24}}`$. This estimate is the cosine
block bound in the scalar local limit calculation.
[Explicit log-concave Fourier bound](https://github.com/ProgramComputer/open-math-research/blob/main/topics/balanced-arrays/adjacent-quotas/scalar.md#an-explicit-scalar-local-limit-estimate)

For a centered real $`y`$ with $`Q_2=\sum_j y_j^2`$,
write $`f_s(y)=\mathbb E e^{i\sum_{j\in I_s}y_j}`$.
The adjacent-size bound

$$
|f_{s+1}(y)-f_s(y)|\le \frac{3Q_2}{2d}
$$

follows by adding a uniform element $`J`$ outside a uniform
$`s`$-subset $`I_s`$. Given $`I_s`$, the conditional mean of $`y_J`$
is $`-L_s/(d-s)`$, where $`L_s=\sum_{j\in I_s}y_j`$.
The linear term is bounded by
$`\mathbb E L_s^2/(d-s)=a_sQ_2/(d-s)\le Q_2/d`$ since
$`\mathbb E L_s=0`$ and $`|e^{iL_s}-1|\le |L_s|`$.
The second-order error uses $`J`$ uniform unconditionally and
is at most $`Q_2/(2d)`$.
Take $`s_0=\lfloor\mu\rfloor`$. On a ball of radius $`b\le2/5`$,

$$
|R(t,y)-\phi(t)f_{s_0}(y)|
\le \frac{3Q_2}{2d}(\sqrt V+1)\le d^{-1/2}
$$

by $`V\le d/4`$. Every remote ball thus has
$`|R(t,y)|\le 1-10^{-25}`$ at $`u\ge10^6`$.

At $`u\ge10^{60}`$ this pointwise estimate already suffices for
the remote integral. With $`\ell=d-1`$, the volume of an
$`\ell`$-dimensional real ball of radius $`b`$ is at most
$`(2\pi e b^2/\ell)^{\ell/2}`$ by integrating a Gaussian which
is at least $`e^{-\ell/2}`$ on that ball. Relative to $`I_0`$,
the union of at most $`d`$ balls has measure at most
$`d(e b^2 A/(d-1))^\nu`$. Since $`A\le n`$ and $`b\le2/5`$,
its logarithm is at most $`u+(d/2)(2+\log(n/d))`$.
Write $`w=n/d\ge u/110`$, by $`A/d\ge u/400`$ and $`a\le.26`$.
The ratio $`(2+\log w)/w`$ decreases on $`w\ge1`$ and is at most
$`(110/u)(2+\log u)<10^{-27}`$, using $`\log u\le\sqrt u`$.
Also $`u/n\ll10^{-27}`$ and $`15A/(dn)\le4/d\ll10^{-27}`$.
It follows that the remote integral divided by $`|G_{\ast}|`$
is at most $`e^{-10^{-26}n}`$.

## Nonprincipal near odd labels

Let $`\Delta=S-S'`$ for an independent copy. Its symmetric
log-concave mass and its survival sequence on nonnegative
integers are log-concave by convolution, or by the decreasing
successive mass ratios for the survival sequence. Put
$`m=\lceil4\sqrt V\rceil\le5\sqrt V`$. The one-sided survival
satisfies $`T(m)\le V/m^2\le1/16`$ and $`T(0)\ge1/2`$.
Iterating survival ratios, with block ratio at most $`1/4`$,
gives $`\Pr(|\Delta|>x)\le8e^{-x/(5\sqrt V)}`$. Integrating
this tail yields $`\mathbb E\Delta^4\le2\cdot10^5 V^2`$.
Differentiating $`1-|\phi(t)|^2`$ therefore gives, for
$`0\le t\sqrt V\le10^{-3}`$,

$$
\mathbb E[\Delta\sin(t\Delta)]
\ge2Vt-\frac{t^3}{6}\mathbb E\Delta^4\ge Vt.
$$

Since the centered characteristic stays nonzero on this
interval, integration gives

$$
|\phi(t)/\phi(t_{\ast})|\le
\exp[-V(t^2-t_{\ast}^2)/4]
\qquad(t_{\ast}\le |t|\le10^{-3}/\sqrt V).
$$

At $`u\ge10^{60}`$ apply the near-chart estimate
$`|I_t|\le4I_0|\phi(t)|^n e^{20d|t|}`$ from
angular-principal-chart.md. Dividing by $`|G_{\ast}|`$ costs at most
an additional $`e^2`$. For odd $`j\ge3`$ we have
$`20\pi j\le(\pi^2/20)L(j^2-1)`$ since $`L\ge2500`$.
The remaining radial penalty is at least
$`(\pi^2/5)L(j^2-1)`$. With $`j=2m+1`$ and $`m\ge1`$ use
$`j^2-1\ge8m`$ to bound the sum over both signs by

$$
8e^2\frac{e^{-(72/5)L}}{1-e^{-(72/5)L}}<1/100 .
$$

In the two principal charts the local errors are each
less than $`|G_{\ast}|/10`$. Adding the three global errors above
proves a total remainder below $`.23|G_{\ast}|<|G_{\ast}|/4`$.

## Larger-radius global version at the original row cutoff

The large cutoff in the preceding combination comes from the
chosen radius and the stated principal estimate. At $`u\ge10^6`$,
use radius $`b=2/5`$. The above off-ball bound already holds.
The remote and nonprincipal near bounds also hold for this
radius by matching the determinant rather than using the ball
volume. The following are direct estimates for those two steps.

On the ball the real part of the exact one-row expansion from
[the single-row expansion](direct-row-expansion.md) gives
$`\log|f_s(y)|\le-a_s B_y`$ with
$`B_y=Q_2/2-1.26Q_4`$. Indeed the quartic has absolute
bound $`(7/24)a_sQ_4`$, and the real remainder is at most
$`6a_sQ_2 M^4\le6b^2a_sQ_4`$. In particular
$`0\le .29Q_2\le B_y\le .5Q_2`$. For precision $`A_0\ge A/2`$,
the zero-sum Gaussian of precision $`A_0`$ satisfies

$$
\mathbb E[\mathbf1_{\Vert Y\Vert \le b}e^{1.26 A_0 Q_4(Y)}]<4.
$$

To check this, write $`Y_j=Z_j-\bar Z`$ with independent
$`Z_j\sim N(0,1/A_0)`$. Insert the independent mean restriction
$`|\bar Z|\le 2/\sqrt{d A_0}`$ at cost at most $`4/3`$.
Then $`|Z_j|\le .401`$ on the ball,
$`|Y_j|^4\le (9/8)^3 |Z_j|^4+9^3|\bar Z|^4`$,
and the deterministic shift in the exponent is below one.
More precisely it is at most $`15000/(d A_0)<.01`$.
The single-coordinate exponent is at most $`2A_0Z_j^4`$,
which on this truncation is at most $`A_0 Z_j^2/3`$.
The elementary expectation bound is $`1+100/A_0`$ using
$`\mathbb E[X^4e^{X^2/3}]=3\cdot3^{5/2}<50`$ for a standard
normal $`X`$. The product and the mean restriction cost at most
$`(4/3)\exp(.01+100d/A_0)<4`$.

For remote labels the adjacent-size bound can be factored against
$`|f_{s_0}(y)|\ge1-a_{s_0}Q_2/2>.97`$, giving
$`|R|\le e^{-10^{-25}}|f_{s_0}(y)|`$.
Take $`A_0=n a_{s_0}`$. Since
$`a_{s_0}\ge a-1/(d-1)\ge a/2`$, the determinant conversion from
$`A_0`$ to $`A`$ costs at most $`e^{2/a}`$. The last expectation
therefore bounds the remote union, relative to $`|G_{\ast}|`$, by
$`4d\exp(-10^{-25}n+2/a+15A/d)<1/100`$.

For near labels the independent-copy covariance identity and the
adjacent-size bound give
$`|R/\phi-\mathbb E f_S(y)|\le 3Q_2 V|t|/(2d|\phi|)`$.
Since $`\mathrm{Var}(a_S)\le V/(d-1)^2`$ and $`B_y\le .08`$,
the scalar Taylor inequality gives

$$
\mathbb E|f_S(y)|
\le\exp\left(-aB_y+\frac{V B_y^2}{(d-1)^2}\right)=U_y,
\qquad U_y>.97.
$$

Thus $`|R|\le |\phi|U_y\exp(2Q_2 V|t|/d)`$.
At an odd label $`j\ge3`$ the two extra log exponents in the
$`n`$th power have sum at most $`nV(.01/d^2+.32|t|/d)`$,
which is less than $`.05 nV(t^2-t_{\ast}^2)`$. For this use
$`j/(j^2-1)\le3/8`$ and $`\pi>3`$. The Gaussian chart
expectation above with $`A_0=A`$ costs at most four, so the
same summable radial bound follows at $`u\ge10^6`$.

This larger-radius version proves global suppression at the
original row cutoff. The [principal-chart comparison on the larger balls](angular-principal-lower.md) completes the proof with a remainder below $`|G_{\ast}|/4`$ there. The local estimate currently cited above
uses radius $`10^{-3}`$ and $`u\ge10^{60}`$.
