# Uniform fourth-moment and angular derivative bounds for a capped binomial

Let $`d\ge1`$, $`0\le r\le d`$, and $`0<p<1`$. Let $`S`$ be
$`\mathrm{Bin}(d,p)`$ conditioned on $`S\le r`$, with mean $`\mu`$,
variance $`V`$, and an independent copy $`S'`$. Then

$$
\mathbb E(S-S')^4
\le V\min\left(\frac{27}{8}d-1,\thinspace{}
               3d+3\sqrt{3d/2}-1\right).
$$

These are uniform finite bounds. They include every positive
tilt, including arbitrarily small $`V`$. The limiting coefficient
$`3`$ in the second bound is sharp even when $`r<d`$.

For the angular consequence assume $`1\le r<d`$, put
$`H(w)=\sum_{s=0}^r\binom ds w^s`$ and $`p=w/(1+w)`$, and take
$`0<\theta\le\pi/d`$. Let $`C_d`$ denote the minimum in the
displayed fourth bound. For $`w>0`$ write
$`L_\theta=\partial_{\log w}\arg H(we^{i\theta})`$,
using the continuous argument in the row-size sector. Then

$$
\frac{\theta V\thinspace{}\max\left\lbrace \mathrm{sinc}(\theta r),\
                           1-C_d\theta^2/12\right\rbrace }
     {\min\left\lbrace 1,\quad 1-V\theta^2+C_d V\theta^4/24\right\rbrace }
\le L_\theta
\le
\frac{\theta V}
     {\max\left\lbrace \cos^2(\theta r/2),\quad 1-V\theta^2\right\rbrace } .
$$

Here $`\mathrm{sinc}(x)=\sin(x)/x`$. In particular, at
$`\theta=\pi/d`$ and $`d\ge3`$,

$$
\theta V\left(1-\frac{\pi^2 C_d}{12 d^2}\right)
\le L_\theta\le \frac{\theta V}{1-\pi^2/(4d)}.
$$

The first bound quantifies the relative angular comparison
without a row-height assumption. The sector bound in the more
detailed statement handles $`d=2`$.

## Exact forward and backward summation by parts

Write $`\pi_s=\Pr(S=s)`$. Use the detailed-balance rates
$`\lambda_s=p(d-s)\mathbf1_{s<r}`$ and
$`\delta_s=(1-p)s`$. For $`s<r`$,

$$
\pi_s\lambda_s=\pi_{s+1}\delta_{s+1}.
$$

The drift is $`\lambda_s-\delta_s=dp-s-p(d-r)\mathbf1_{s=r}`$.
Detailed balance gives zero mean drift and hence

$$
dp-\mu=p(d-r)\pi_r\ge0,\qquad
\mathbb E\lambda_S=\mathbb E\delta_S=(1-p)\mu .
$$

Define the forward coefficient
$`\tau_s=\pi_s^{-1}\sum_{j=0}^s(\mu-j)\pi_j`$,
and the backward coefficient
$`\bar\tau_s=\pi_{s-1}\tau_{s-1}/\pi_s`$, with the
out-of-support term interpreted as zero. The partial sum defining
$`\tau_s`$ is nonnegative since the mean on the lower segment is
at most the full mean. Also $`\tau_r=0`$.
Telescoping the drift on $`0,\ldots,s`$ for $`s<r`$ gives

$$
\tau_s=\lambda_s-(dp-\mu)\frac{\Pr(S\le s)}{\pi_s}.
$$

In particular $`0\le\tau_s\le\lambda_s`$ including the top
endpoint, and detailed balance gives $`0\le\bar\tau_s\le\delta_s`$.
The difference is exactly $`\tau_s-\bar\tau_s=\mu-s`$.

Let $`Z=S-\mu`$. Summation by parts with a test function $`f`$ is

$$
\mathbb E[Zf(S)]
=\mathbb E[\tau_S(f(S+1)-f(S))]
=\mathbb E[\bar\tau_S(f(S)-f(S-1))].
$$

Applying it to $`f(s)=s`$ proves
$`\mathbb E\tau_S=\mathbb E\bar\tau_S=V`$, so in particular
$`V\le(1-p)\mu\le dp(1-p)`$.
Applying both identities to $`f(s)=(s-\mu)^3`$ and averaging
gives the exact identity

$$
\mathbb E Z^4=\frac32\mathbb E[(\tau_S+\bar\tau_S)Z^2]-V/2.
$$

Indeed the forward and backward differences are respectively
$`3Z^2+3Z+1`$ and $`3Z^2-3Z+1`$. The opposite linear terms combine
to $`-\frac32\mathbb E Z^2`$ and the constant terms give $`V`$.
This averaging removes the need to estimate small-variance
third moments separately.

## The two uniform fourth bounds

Since $\lambda_s+\delta_s\le dp+(1-2p)s\le
d\max(p,1-p)$, the exact identity gives
$`\mathbb E Z^4\le (\frac32d\max(p,1-p)-\frac12)V`$.
Independence gives $`\mathbb E(S-S')^4=2\mathbb E Z^4+6V^2`$.
Therefore

$$
\frac{\mathbb E(S-S')^4}{V}
\le 3d\max(p,1-p)-1+6dp(1-p)\le\frac{27}{8}d-1
$$

when $`V>0`$. For the final inequality put $`q=\max(p,1-p)`$
and maximize $`3q+6q(1-q)=9q-6q^2`$ on $`[1/2,1]`$.

Alternatively retain the affine expression
$`dp+(1-2p)s`$ in the exact identity. Then

$$
\frac{\mathbb E(S-S')^4}{V}
\le 3dp+(9-12p)\mu-1
   +3|1-2p|\thinspace{}\frac{|\mathbb E Z^3|}{V}.
$$

We used $`V\le(1-p)\mu`$. The first two terms are at most
$`3d`$ since for $`p\le3/4`$ one can substitute $`\mu\le dp`$
to get $`12dp(1-p)\le3d`$, and for $`p\ge3/4`$ the coefficient
of $`\mu`$ is nonpositive. By Cauchy–Schwarz and the earlier
fourth bound,
$`|\mathbb E Z^3|/V\le\sqrt{\mathbb E Z^4/V}\le\sqrt{3d/2}`$.
This proves the second estimate. All moment assertions at $`V=0`$
hold directly.

For sharpness in leading order take $`p=1/2`$, $`r=d-1`$.
The conditioning deletes a mass $`2^{-d}`$. Its effect on
variance is $`O(d^2 2^{-d})`$ and on the fourth moment of
the independent difference is $`O(d^4 2^{-d})`$, by bounded
support and coupling the two copies. Without conditioning,
the variance is $`d/4`$ and the independent difference has
fourth moment $`3d^2/4-d/4`$, by writing it as a sum of iid
differences of Bernoulli variables. Thus the fourth moment
divided by $`dV`$ tends to $`3`$ along proper caps.

## Angular derivative and its two-sided estimates

Let $`\Delta=S-S'`$ and $`\phi=\mathbb E e^{i\theta S}`$.
Since all row phases lie in a sector of width $`\theta r<\pi`$,
$`|\phi|\ge\cos(\theta r/2)>0`$. Differentiate in $`\log w`$
and multiply the quotient by $`\bar\phi`$ to obtain the exact
symmetrized derivative

$$
L_\theta
= \Im\frac{\mathbb E[S e^{i\theta S}]}{\phi}
= \frac{\mathbb E[\Delta\sin(\theta\Delta)]}{2\thinspace{}\mathbb E\cos(\theta\Delta)} .
$$

This derivative is strictly positive when $`V>0`$, since
$`|\Delta|\theta\le r\theta<\pi`$. For the lower bound on
the numerator divided by two, $`\mathrm{sinc}`$ decreases
on $`[0,\pi]`$, and $`\sin x\ge x-x^3/6`$ for $`x\ge0`$.
Use $`\mathbb E\Delta^2=2V`$ and the fourth bound to get
both $`\theta V\,\mathrm{sinc}(\theta r)`$ and
$`\theta V(1-C_d\theta^2/12)`$.
The upper bound is $`\theta V`$ since $`\sin x\le x`$ for
$`x\ge0`$. The denominator $`\mathbb E\cos(\theta\Delta)=|\phi|^2`$
is bounded below by $`\cos^2(\theta r/2)`$ and
$`1-V\theta^2`$, and above by $`1`$ and
$`1-V\theta^2+C_d V\theta^4/24`$ using the quadratic and
quartic cosine inequalities. These give the stated bounds.

With $`q_s=s(d-s)/[d(d-1)]`$, the $`q_s`$-weighted tilted
law is exactly one plus a $`\mathrm{Bin}(d-2,p)`$
conditioned to be at most $`r-1`$, because
$`q_s\binom ds=\binom{d-2}{s-1}`$.
For $`r=1`$ it is deterministic. In all other cases the
same unweighted fourth-moment estimate applies with
ambient size $`d-2`$. The angular proof only needs the sector
width to be smaller than $`\pi`$, which holds at the original
$`\theta=\pi/d`$ even if the reduced cap is full.

For example, if a separate comparison gives weighted variance
$`\widetilde V\le V`$, the estimates above imply positivity of
the derivative of $`(n+\nu)\arg H-\nu\arg Q`$ for $`n\ge3`$ and
$`d\ge39`$, where $`\nu=(d-1)/2`$ and $`Q`$ is the weighted row
polynomial. Indeed for $`\theta=\pi/d`$ one has
$`L_\theta\ge\theta V(1-45/(16d))`$ and
$`\widetilde L_\theta\le\theta V/(1-5/(2d))`$ by $`\pi^2<10`$.
The factors satisfy

$$
\left(1+\frac6{d-1}\right)
\left(1-\frac{45}{16d}\right)\left(1-\frac5{2d}\right)
\ge
\left(1+\frac6{d-1}\right)\left(1-\frac{85}{16d}\right)>1.
$$

The last inequality is $`11d>425`$. This implication relies on
the separate weighted variance comparison.

I checked the exact forward/backward moment identity and the
rational fourth bound on all caps through $`d=28`$, using seven
positive rational tilts at each cap. The proof applies uniformly
over the whole parameter range. For the existing asymptotic uses
of the angular derivative, see the
[transverse angular argument](https://github.com/ProgramComputer/open-math-research/blob/main/topics/balanced-arrays/eventual-all/analytic-angular-signs.md).
