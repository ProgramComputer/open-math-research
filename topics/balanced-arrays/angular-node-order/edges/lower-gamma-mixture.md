# Effective reduction of the lower hyper-Bessel sign problem

Put $\theta=\pi/d$, $U=(\theta/\sin\theta)(k+(d-1)/(2d))$,
and $F_d(q)=\sum_{m\ge0}q^m/(m!)^d$. Then
$(-1)^kF_d(-U^d)>0$ in each of the following ranges:

- $d=2$ and all $k\ge1$.
- $d\ge128$ and all $k\ge1$.
- $d\ge8$ and $k\ge128$.
- $d\ge3$ and $k\ge100d$.
- $d\ge4$ and $1\le k\le d/4$.

Hence only the following finite strip remains. For $3\le d\le7$,
check $d/4<k<100d$. For $8\le d\le127$, check $d/4<k<128$.

## Positive mixture and its tilted moments

Let $s=\lfloor(d-1)/2\rfloor$, $b=s/d$,
$a_i=(s+i)/d$ for $1\le i\le d$, and
$\kappa=d-\sum_i a_i\in\{0,1/2\}$. Define
$T(m)=\prod_{i=1}^d\Gamma(m+a_i)/\Gamma(m+1)^d$.
The digamma difference identity and integration give

$$
\frac{T(m)}{T(0)}
=\exp\!\left[-\int_0^\infty(1-e^{-my})K(y)\frac{dy}{y}\right],
\qquad
K(y)=\frac{\sum_i e^{-a_i y}-d e^{-y}}{1-e^{-y}}.
$$

Indeed differentiating the logarithm gives the differences of the
digamma integral, with convergence at zero by cancellation.
The average of the $a_i$ is at most one, so Jensen gives $K(y)\ge0$.
The measure $K(y)dy/y$ has finite integral against $\min(1,y)$,
since $K$ is bounded near zero and decays exponentially at
infinity. One can construct a nonnegative random variable $X$
with this Laplace transform by summing Poisson jumps with
that intensity. Equivalently, truncate the intensity away from
zero and take the limit of the compound Poisson sums. The omitted
small jumps have expectation tending to zero. In particular
$T(m)/T(0)$ is the $m$th moment of $e^{-X}$.

Multiplication of the gamma function gives
$\prod_i\Gamma(m+a_i)=(2\pi)^{(d-1)/2}
 d^{-dm-s-1/2}\Gamma(dm+s+1)$.
Consequently, with $E_{d,s}$ as in
[the upper sign lemma](angular-upper-edge-sign.md), we have

$$
F_d(-U^d)=
T(0)(2\pi)^{-(d-1)/2}d^{s+1/2}(dU)^{-s}
\mathbb E\big[e^{bX} E_{d,s}(dU e^{-X/d})\big].
$$

Termwise expectation is justified by the absolute convergence of
the input power series using the exact gamma identity. Also
$\mathbb E e^{bX}$ is finite, because $a_1-b=1/d>0$ in the
large-$y$ part of the intensity. Absorb this factor by tilting the
law of $X$ by $e^{bX}$. Denote the resulting law by $\mathbb P_b$.
Its Laplace transform $L_b(q)$ has the same formula with
$K_b(y)=e^{by}K(y)$, namely

$$
K_b(y)=\frac{\sum_{i=1}^d e^{-iy/d}-d e^{-(1-b)y}}{1-e^{-y}}.
$$

For $0<y\le1$, Taylor's inequalities give a numerator at most
$\kappa y+dy^2/2$. Since $1/(1-e^{-y})\le 1/y+1$, this yields
$K_b(y)\le\kappa+(d+1)y$. For $y\ge1$, use the exponential or the
infinite geometric bound on the numerator to get
$K_b(y)\le2d\min(e^{-y/d},1/y)$. Thus for $q>0$, under the
probability law obtained from $\mathbb P_b$ by weighting by $e^{-qX}$,

$$
\mathbb E_{b,q}X\le \frac{\kappa}{q}+\frac{d+1}{q^2}
                    +\frac{2d e^{-q}}{q}.
$$

This follows by differentiating $-\log L_b(q)$. Another direct
integration gives

$$
-\log L_b(T)\le 3d+2+\log(1+T)\qquad(T>0).
$$

On $y\le1$ the constant term contributes at most
$\kappa[1+\log(1+T)]$, by splitting at $1/(1+T)$, and the
linear term contributes at most $d+1$. The integral on $y\ge1$
is at most $2d$. Adding these bounds proves the display.

## Angular dominance under the mixture

Assume $d\ge3$ and put $Z=e^{-X/d}$, $T=U\cos\theta>0$.
After the finite odd-root filter, set
$M=\mathbb E_b e^{dTZ}>0$. Normalize by the positive principal
amplitude $2M/d$, and introduce the probability law with density
$e^{dTZ}/M$ relative to $\mathbb P_b$. The expected cosine of
the signed principal conjugate pair under this law is

$$
\mathbb E\cos\bigl(\epsilon-dU\sin\theta(1-Z)\bigr),
\qquad
\epsilon=((d-1)/2-s)\theta\in\{0,\theta/2\}.
$$

For $0<c<1$, call $Z\ge c$ the retained event, and write $\tau$
for the probability of its complement under the last law.
Since $g(X)=dT(1-e^{-X/d})\le TX$, the normalizing expectation
after removing $e^{dT}$ is at least $L_b(T)$. The complement
satisfies $g(X)>dT(1-c)$, so

$$
\tau\le \exp[-dT(1-c)+3d+2+\log(1+T)] .
$$

On the retained interval the derivative $g'(X)=T e^{-X/d}$
is at least $q=cT$. Thus on that interval the likelihood
ratio of the nonlinear tilt to the linear tilt $e^{-qX}$ is
nonincreasing. Its retained conditional mean of $X$ is bounded
by $\mathbb E_{b,q}X$, since conditioning the linear tilt on an
initial interval decreases its mean. It follows from
$1-Z\le X/d$ and the Lipschitz bound one for cosine that the
signed principal pair is at least

$$
\cos\epsilon-U\sin\theta\,\mathbb E_{b,q}X-2\tau
$$

in the normalized units.

At any odd representative $\beta=(2\ell+1)\theta$ with
$\ell\ge1$ and $\beta\le\pi$,
$\cos\theta-\cos\beta\ge8\ell^2/d^2$ by the sine bound
in the upper sign lemma. Its averaged modulus relative to the
principal modulus gains $\exp[-dU(\cos\theta-\cos\beta)Z]$.
Counting the odd singleton at $\pi$ at most twice, all nonprincipal
labels together cost at most

$$
\sum_{\ell\ge1} \exp[-8c(U/d)\ell^2]+d\tau .
$$

These bounds concern the positive mixture after normalization and
take no absolute value of the signed principal cosine.

## Explicit ranges

For $d\ge128$ and $k\ge d/4$, set $c=1/2$. We have
$U\ge d/4$, $\cos\theta\ge .98$, $T\ge31$ and
$q\ge .49U$. Substitution in the mean bound gives
$U\mathbb E_{b,q}X<20$. For example the first term is at most
$.5/.49$, the second at most $4(1+1/128)/.49^2$ and the third
at most $(2/.49)d\cdot24/(.49d/4)^4<1$, using the fourth Taylor
term for $e^q$. The principal cosine loses at most
$20\pi/d<.492$ from this mean. The complement bound gives
$\tau<e^{-11d}$ using $\log(1+T)\le T$ and $T\ge31$.
The nonprincipal sum on the retained event is less than $.4$:
bound it by $e^{-1}+e^{-4}/(1-e^{-3})$ and use $e>8/3$.
Since $\cos\epsilon>.999$, the total signed lower bound is positive.

For $d\ge8$, $k\ge128$ and $k\ge d/4$, again set $c=1/2$.
The inequalities $\cos\theta\ge 1-\pi^2/(2d^2)>.92$
and $U\ge128$ give $T>117$ and $q>.46U$. Use
$\sin\theta\le\pi/d$ and the fourth Taylor term for the last
term of the mean bound. The three pieces of the phase loss
are bounded by the following rational comparisons, using
$\pi<22/7$:

$$
\begin{aligned}
\frac{22}{7}\frac{1}{2\cdot .46\cdot 8}&<.434,\\
\frac{22}{7}\frac{9}{8\cdot .46^2\cdot128}&<.131,\\
\frac{44}{7\cdot .46}\frac{24}{(.46\cdot128)^4}&<.001.
\end{aligned}
$$

The complement loss obeys $\tau<e^{-50d}$ because
$\log(1+T)\le T/4$ and $(d/2-1/4)T-3d-2>50d$ at
$d\ge8$, $T>117$. Thus $(d+2)\tau<.001$, for example
by $e^{50d}\ge(50d)^3/6$.
The retained nonprincipal contribution is below $.4$ as before,
and $\cos\epsilon\ge1-10/512>.98$. The sum
$.434+.131+.001+.001+.4=.967$ of losses is strictly smaller.

For $d\ge3$ and $k\ge100d$, set $c=3/4$. Then $U\ge100d$,
$T\ge U/2$ and the complement bound gives $\tau<e^{-20d}$.
Indeed $T\ge150$, $\log(1+T)\le T/4$, and the resulting
exponent is at most $-(d-1)T/4+3d+2$.
The retained nonprincipal sum is below $.01$ by
$8cU/d\ge600$ and the bound by a geometric series.
If $d\ge4$, then $q\ge U/2$ and
$U\mathbb E_{b,q}X<1.052$. Here the small last term follows from
the fourth Taylor bound and $U\ge100d$.
Thus the cosine loses less than $.75$ because
$\sin\theta\le1/\sqrt2$, while $\cos\epsilon>.92$.
If $d=3$, then $\kappa=0$, $q=3U/8$ and
$U\mathbb E_{b,q}X<.1$ by $U\ge300$.
Here $\cos\epsilon=1$. The inequalities prove positivity in
both cases.

For $d\ge8$, $1\le k\le d/4$ the
[adjacent-term estimate](phase-edge-review.md#positive-lower-signs-for-growing-dimension)
already proves the sign. For $4\le d\le7$ this range contains
only $k=1$. We have $11/8\le U\le27/16$ by the same sine
inequality. The first outward ratios sum to at most
$(8/11)^4+(27/32)^4<1$, so the same pairing works.

Finally at $d=2$, the Poisson integral gives $F_2(-U^2)=J_0(2U)$.
For $t=2U$, the function $y=\sqrt t\,J_0(t)$ satisfies
$y''+(1+1/(4t^2))y=0$. The equation follows by differentiating
the absolutely convergent series. Its Prüfer angle satisfies
$\psi'=1+\cos^2\psi/(4t^2)$. Applying stationary phase to the
exact cosine integral and to its derivative gives a continuous
lift with $\psi(t)-(t-\pi/4)\to0$ at infinity. Integration
therefore gives $|\psi(t)-(t-\pi/4)|\le1/(4t)$.
Since $t-\pi/4=k\pi$ at the test value, the sign is correct.
