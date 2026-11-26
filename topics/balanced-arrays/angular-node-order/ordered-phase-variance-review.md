# Independent review of the weighted variance bound and phase ordering

The universal skewness bound and its application to the holes law
are valid. The alternative low-mean argument below and the finite
angular estimates give strict phase monotonicity for $`n\ge d\ge36`$,
every proper cap $`1\le r<d`$, and every positive tilt.
This is an ordering result for the phase used in the angular test.
It supplies no additional estimate for the sign of the Fourier
integral at a phase node.

## Universal log-concave skewness

Let $`T`$ be integer-valued with positive, log-concave masses $`p_j`$
on $`[0,r]`$, mean $`m`$, variance $`V`$, and forward coefficient

$$
\tau_j=\frac{\sum_{i\le j}(m-i)p_i}{p_j}
      =\frac{\Pr(T>j)}{p_j}\bigl(\mathbb E[T\mid T>j]-m\bigr)
\qquad(j<r).
$$

The version for an interval with a different lower endpoint follows
by translation. The coefficients are nonnegative and $`\tau_r=0`$.
For $`k=j+1`$, the law of $`T-k`$ conditional on $`T\ge k`$
is stochastically dominated by $`T`$. Indeed its likelihood ratio to
$`p_i`$ is proportional to $`p_{k+i}/p_i`$, decreasing in $`i`$ because
the successive ratios of $`p`$ decrease. The likelihood ratio becomes
zero past the upper endpoint. This likelihood-ratio comparison gives
$`\mathbb E[T-k\mid T\ge k]\le m`$ and consequently

$$
\tau_j\le(j+1)\Pr(T>j)/p_j.
$$

Put $`R=p_{j+1}/p_j`$ for $`j<r`$. When $`R<1`$ the tail ratio is at
most $`R/(1-R)`$ by a geometric series. The exact adjacent relation is
$`\tau_{j+1}-\tau_j=(1/R-1)\tau_j+m-j-1`$.
It is at most $`m`$ when $`R<1`$ by the stated tail bound, and when
$`R\ge1`$ by $`\tau_j\ge0`$. Thus $`mj-\tau_j`$ is nondecreasing.
The independent-copy covariance identity gives
$`\mathrm{Cov}(T,\tau_T)\le mV`$.

The forward summation-by-parts identity applied to $`f(j)=(j-m)^2`$
gives $`\kappa_3(T)=2\mathrm{Cov}(T,\tau_T)+V`$ because
$`\mathbb E\tau_T=V`$. Hence $`\kappa_3(T)\le(1+2m)V`$.
The argument includes the degenerate interval as the zero-variance
case. Interval support matters for the likelihood-ratio step.

## Weighting with the row quadratic

Use $`S=\mathrm{Bin}(d,p)\mid\{S\le r\}`$,
$`\mu=\mathbb ES`$, $`V=\mathrm{Var}(S)`$, and let
$`\widetilde V`$ be its variance after weighting by $`q(s)=s(d-s)`$.
The identities reviewed in
[ordered-phase-fourth.md](ordered-phase-fourth.md)
give $`V\le(1-p)\mu`$ and $`\mu\le dp`$, so
$`V\le\mu(d-\mu)/d`$. The weighted law is exactly one plus
$`\mathrm{Bin}(d-2,p)`$ capped at $`r-1`$.

More generally let $`Y`$ be either $`S`$ or $`d-S`$, with mean $`h`$,
so $`q(Y)`$ gives the same variance after weighting. Write
$`Z=Y-h`$, $`W=\mathbb E q(Y)=h(d-h)-V`$, and
$`\kappa_3=\mathbb E Z^3`$. Expanding the weighted variance gives

$$
\widetilde V-V
=\frac{(d-2h)\kappa_3-(\mathbb E Z^4-V^2)}{W}
 -\left(\frac{\mathbb E[q(Y)Z]}{W}\right)^2.
$$

The fourth correction is nonpositive by Cauchy–Schwarz.
The same matched-mean bound gives $`W\ge(d-1)h(d-h)/d`$.

If $`\mu\ge d/2`$, take $`Y=d-S`$ so $`h\le d/2`$.
Its minimum is $`c=d-r\ge1`$. Applying the skewness result to
$`Y-c`$ gives $`\kappa_3\le(1+2(h-c))V\le(2h-1)V`$.
Thus

$$
\frac{\widetilde V}{V}\le
1+\frac{d}{d-1}\frac{d-2h}{d-h}(2-1/h).
$$

The gap in the unnormalized factor from two is

$$
2-\frac{d-2h}{d-h}(2-1/h)
=\frac1h+\frac{2h-1}{d-h}
\ge \frac1h+\frac{2h}{d}-\frac1d
\ge 2\sqrt{2/d}-1/d.
$$

The first inequality uses $`h\ge1`$ and the second is AM–GM.
Consequently, throughout the high-mean branch,

$$
\frac{\widetilde V}{V}
\le 3-\frac{2\sqrt{2d}-3}{d-1}.
$$

## An independent low-mean estimate

For the upper-capped binomial, the forward coefficient from
ordered-phase-fourth.md is
$`\tau_s=p(d-s)-(dp-\mu)F(s)/\pi_s`$ for $`s<r`$,
where $`F(s)=\Pr(S\le s)`$ and $`\pi_s=\Pr(S=s)`$.
The ratio $`F(s)/\pi_s`$ increases in $`s`$.
Indeed for each fixed $`j\ge0`$, the term $`\pi_{s-j}/\pi_s`$
in its sum increases with $`s`$ wherever it is defined, because
each successive ratio of $`\pi`$ decreases. New terms are
nonnegative. The first term of $`\tau_s`$ decreases in $`s`$,
and $`dp-\mu\ge0`$. Thus $`\tau_s`$ is nonincreasing, including
$`\tau_r=0`$. The Stein identity then gives
$`\kappa_3(S)=V+2\mathrm{Cov}(S,\tau_S)\le V`$.

If $`0<\mu\le31/50`$, let $`S^*`$ be size-biased by $`S`$.
Then $`\mathbb E(S^*-1)=\mu+V/\mu-1\le\mu`$.
Further reweighting by the decreasing function $`d-s`$ gives
the quadratic-weighted law and can only decrease the mean.
Since this weighted law minus one is a capped binomial,
its variance is at most its mean, so $`\widetilde V\le\mu`$.
The integer inequality $`S^2\ge S`$ gives
$`V\ge\mu(1-\mu)`$ and hence $`\widetilde V/V\le50/19`$.

If $`31/50\le\mu\le d/2`$, apply the quadratic expansion with
$`Y=S`$ and $`\kappa_3(S)\le V`$. It gives

$$
\frac{\widetilde V}{V}\le
1+\frac{d}{d-1}\frac{d-2\mu}{\mu(d-\mu)}.
$$

The product $`(d-2\mu)/(d-\mu)`$ and $`1/\mu`$ are both
nonnegative decreasing factors on this interval, so the bound
is largest at $`t=31/50`$. At that endpoint,
$`d(d-2t)/((d-1)(d-t))\le1+(1-t)/(d-1)`$,
since $`d(1-t)-t\le(1-t)(d-t)`$.
Thus for $`d\ge36`$ this branch gives at most
$`1+50/31+19/(31(d-1))<50/19`$. Both low-mean subcases
therefore give $`\widetilde V/V\le50/19`$.

## Explicit phase threshold

Take $`\theta=\pi/d`$ and $`\nu=(d-1)/2`$. Write $`H`$ for the
capped row polynomial and $`Q`$ for its quadratic-weighted version.
The phase is $`(n+\nu)\arg H(we^{i\theta})-\nu\arg Q(we^{i\theta})`$.
Let $`L,\widetilde L`$ be the respective derivatives in $`\log w`$.
The fourth-moment and angular inequalities yield

$$
L\ge\theta V\left(1-\frac{45}{16d}\right),\qquad
\widetilde L\le
\frac{\theta\widetilde V}{1-5/(2d)+5/d^2}.
$$

The first bound uses $`27d/8`$ for the fourth-moment coefficient
and $`\pi^2<10`$. The second uses $`\widetilde V\le(d-2)/4`$ from
the reduced binomial. Its angular width is smaller than $`\pi`$
at the original angle, even if the reduced cap is full.
For $`n\ge d`$ it is sufficient to prove $`\widetilde V/V<A_d`$, where

$$
A_d=\left(3+\frac{2}{d-1}\right)
     \left(1-\frac{45}{16d}\right)
     \left(1-\frac5{2d}+\frac5{d^2}\right).
$$

For the low-mean branch, let $`x=1/d\le1/36`$. This expression is
$`(3-x)(1-45x/16)(1-5x/2+5x^2)/(1-x)`$.
Its logarithmic derivative in $`x`$ is at most
$`1/(1-x)-45/16<0`$, because the two remaining logarithmic
terms are negative and the term from $`1-45x/16`$ is
at most $`-45/16`$. Thus $`A_d\ge A_{36}=1092149/414720`$.
Its difference from $`50/19`$ is $`14831/7879680>0`$.

For the high-mean branch, the weaker lower bound
$`A_d\ge(3+2/(d-1))(1-85/(16d))`$ suffices.
Subtracting the high-mean variance bound leaves

$$
\frac{2\sqrt{2d}-1-(85/16)(3-1/d)}{d-1}>0
\qquad(d\ge36),
$$

since $`2\sqrt{72}-1>255/16`$ already at the lower endpoint.
This completes the strict derivative comparison for all positive
tilts and proper caps when $`n\ge d\ge36`$.

The skewness and variance identities were also replayed with
exact rational weights on finite samples. The threshold checks
use only rational arithmetic after squaring the positive
square-root endpoint comparison.

## Independent finite audit, 26 November 2026

The finite certificate covers every proper cap at $`2\le d\le35`$.
Together with the analytic threshold above, it proves strict
phase ordering at every positive tilt whenever $`n\ge d\ge2`$.
Both replays below checked 595 cap-dimension pairs, 26,775
strictly positive interior coefficients, and 1,190 structural
endpoint zeros.

### Coefficient derivation and denominators

For $`z=w e^{i\theta}`$, $`\theta=\pi/d`$, write
$`F(z)=\sum_i f_i z^i`$ for either truncated binomial polynomial.
Then $`L_F=|F(z)|^2>0`$. Positivity follows because the terms lie
in a sector of width less than $`\pi`$, and their coefficients
and $`w`$ are positive. The numerator of the derivative in
$`\log w`$ is $`K_F=\Im(zF'(z)\overline{F(z)})`$. In the ordered
pair $`(i,j)`$ the contribution to the coefficient at $`i+j`$ is
$`i f_i f_j\sin((i-j)\theta)`$. The diagonal contributes zero.
Adding pair $`(j,i)`$ to pair $`(i,j)`$ for $`i>j`$ gives exactly
$`(i-j)f_if_j\sin((i-j)\theta)`$. For $`L_F`$ the ordered pair
contribution is $`f_if_j\cos((i-j)\theta)`$, so the diagonal
contributes once and the off-diagonal pairs contribute twice.

The weighted polynomial is $`Q(z)=z B(z)`$ with
$`B(z)=\sum_{j=0}^{r-1}\binom{d-2}{j}z^j`$, by the exact
quadratic-weight binomial identity. The factor $`z`$ has constant
argument along the ray. Thus the derivative is
$`(n+\nu)K_H/L_H-\nu K_B/L_B`$, where $`\nu=(d-1)/2`$.
Multiplication by $`2L_HL_B`$ is legitimate and gives at $`n=d`$
the numerator $`(3d-1)K_HL_B-(d-1)K_BL_H`$.
The finite certificate's stronger inequality
$`2K_HL_B-K_BL_H>0`$ proves this derivative strictly positive.
Indeed $`K_H>0`$ since its nonzero sine pairs have gap less than
$`d`$. Increasing $`n`$ preserves the derivative sign.

### Original interval checker

I read the trigonometric derivation in
[ordered-phase-algebra.md](ordered-phase-algebra.md) and audited
[verify-phase-order.py](verify-phase-order.py).
The incremental appends form the complete coefficient lists
for degrees $`r`$ and $`r-1`$, including the $`B=1`$ case at $`r=1`$.
Each new coefficient is paired exactly once with every earlier
coefficient. The new diagonal slot lies beyond every new
off-diagonal index, so writing that diagonal directly preserves
all earlier terms. At each cap both convolutions have degrees
indexed from $`0`$ to $`4r-2`$. Their two endpoints vanish because
the $`K`$ arrays have zero first and last entries. Their
$`4r-3`$ interior positions are all tested.

The Machin identity holds in the checked branch.
$`\tan(4\arctan(1/5))=120/119`$, so the tangent after subtraction
of $`\arctan(1/239)`$ is one, and the angle lies in $`(0,\pi/2)`$.
The arctangent partial sums enclose the respective arguments by
alternation. The sine and cosine positive term magnitudes are
enclosed with outward integer rounding and alternating signs.
The tail from the first omitted term alternates with decreasing
magnitude on the Taylor interval. The argument-rounding
allowance follows from the unit Lipschitz bounds. Reflection
and the exact midpoint cover every remaining gap in
$`\{0,\ldots,d-1\}`$.

The lower convolution uses the two certified nonnegative lower
arrays. For the upper convolution, the exact $`K_B`$ coefficients
are nonnegative by the positive sine factors. Together with
the checked nonnegative upper endpoints, this gives a valid
upper product coefficient even if a cosine coefficient were
negative. The two products are at the same squared scale.
The radix width exceeds the bit bound for a product of the two
largest entries times the maximum number of coefficient summands.
Thus the packed integer multiplication introduces no carry
between digits.

### Independent exact replay

[verify-phase-order-chebyshev.py](verify-phase-order-chebyshev.py)
uses no Taylor series or Machin approximation. For $`d\ge3`$,
the largest root of $`U_{d-1}(x)`$, with $`U`$ the Chebyshev polynomial
of the second kind, is $`\cos(\pi/d)`$. It lies in the interval
$`(1-8/d^2,1)`$, since $`\cos(\pi/d)>1-5/d^2`$.
The second largest root lies below its left endpoint, since
$`1-\cos(2\pi/d)=2\sin^2(\pi/d)>8/d^2`$ by the sine chord bound.
Thus that interval isolates the largest root. The checker
bisects with exact integer signs of the scaled $`U_{d-1}`$ recurrence.
It treats $`d=2`$ at its exact base value zero.

After isolating the root, the checker obtains
$`\cos(j\theta)=T_j(\cos\theta)`$ and
$`\sin(j\theta)/\sin\theta=U_{j-1}(\cos\theta)`$ by outward-rounded
Chebyshev recurrences at scale $`2^{256}`$. It divides the two $`K`$
arrays by the same positive $`\sin\theta`$, preserving signs.
It constructs the coefficients from all ordered pairs and
performs ordinary signed interval convolution using all four
corner products for each pair of coefficient intervals.
This avoids the packed convolution and any requirement that
the cosine coefficient arrays be nonnegative.

Run from this directory with Python 3.

~~~sh
python3 -B verify-phase-order.py --max-d 35
python3 -B verify-phase-order-chebyshev.py
~~~

The mathematical inputs are exactly $`d=2,\ldots,35`$ and
$`r=1,\ldots,d-1`$, with coefficient rows $`\binom dj`$ and
$`\binom{d-2}{j}`$ and ray angle $`\pi/d`$. The first run used
SHA-256
`3ae4533d5b66adad53609e658ac453420f754cb5c2cbeb11265b61509d275e28`
for the original script. The independent script used
`f9fff96180ef36328cd61fc4abd84d209cc2378370816a5c2e4eef3e73ff3ad2`.
