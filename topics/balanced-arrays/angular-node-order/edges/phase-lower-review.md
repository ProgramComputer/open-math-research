# Independent review of the lower-edge finite-exception argument

I checked the lower limiting functions in [phase-edge-review.md](phase-edge-review.md).
The argument proves that only finitely many integer pairs $(d,k)$,
$d\ge2$ and $k\ge1$, can fail
$(-1)^k F_d(-U_{d,k}^d)>0$, where
$F_d(q)=\sum_{m\ge0}q^m/(m!)^d$ and
$U_{d,k}=(\theta/\sin\theta)(k+(d-1)/(2d))$, $\theta=\pi/d$.
I found no mathematical gap in this finite-exception claim.
The proof supplies neither an explicit finite cutoff nor a
certificate for every lower limiting sign. My review concerns
the lower limiting function. The upper limiting sign and the
transfer to signs of array polynomials are separate arguments.

## Poisson integral and tails for growing dimension

Absolute convergence gives
$F_d(-U^d)=\int_{\prod z_j=-1}\exp(U\sum_j z_j)\,dz$.
Indeed Haar projection retains exactly the monomials with
all exponents equal, and the common exponent $m$ contributes
$(\prod z_j)^m=(-1)^m$. The period vectors
$2\pi(e_j-e_d)$ in the sum-zero angular hyperplane have Gram
determinant $d(2\pi)^{2(d-1)}$. Thus the normalized Gaussian
integral of precision $U$ is
$I=(2\pi U)^{-(d-1)/2}/\sqrt d$.

On the complement of disjoint balls of fixed radius $b$ around
the odd diagonal angles, $D_z=\sum_j|z_j-\bar z|^2\ge b^2/3$.
One can recover a zero-sum short lift if $D_z<b^2/3$
by choosing relative angles to $\arg\bar z$ and subtracting their
mean. Their sum of squares is at most $3D_z$ by the chord bound.
At an anchor minimizing $|z_i-\bar z|$,
$\sum_{j\ne i}|\arg(z_j/z_i)|^2\le 5D_z$.
The relative-angle map pushes normalized Haar forward to
normalized Haar, since the equation for $d\arg z_i$ always
has a solution and the map is a group homomorphism up to translation.
In particular there is no extra factor from its $d$-fold covering.

The pointwise envelope is $e^{Ud-UD_z/2}$. Using one half of its
penalty for the complement condition gives $e^{-Ub^2/12}$.
The other half yields Gaussian precision $U/10$ in the
$d-1$ anchor coordinates. Their normalized integral is exactly
at most $I\sqrt d\,10^{(d-1)/2}$ after extending the coordinate
ranges to the real line. Summing over anchors gives the factor
$d^{3/2}10^{(d-1)/2}$ in the proof. Relative to
$I e^{Ud\cos\theta}$ the log bound is at most

$$
-\frac{Ub^2}{12}+\frac{\pi^2U}{2d}
+\frac{d-1}{2}\log 10+\frac32\log d.
$$

This tends to minus infinity when $d\to\infty$ and $U/d\to\infty$
with fixed $b>0$. This step does not require a bound on how
quickly $U/d$ tends to infinity.

Within a chart, the linear transverse term cancels exactly.
The Gaussian has complex precision $Ue^{it}$ and real precision
$A=U\cos t$ in its modulus. I checked the fourth-power exponential
moment by inserting the independent bound on the mean of the
underlying normal coordinates and absorbing the truncated
one-coordinate quartic exponent in a fraction of the Gaussian
quadratic. The chi-square quadratic moment costs $e^{O(dt^2)}$.
One first fixes the multipliers needed for Cauchy–Schwarz, then
chooses the common ball radius and angular interval sufficiently
small for those multipliers. Both remain fixed in the limiting
argument. The real Gaussian determinant conversion costs
$\cos(t)^{-(d-1)/2}=e^{O(dt^2)}$ as used in the proof.

At nonprincipal near angles $|t|=j\theta$, odd $j\ge3$, the
loss $O(dt^2)$ is absorbed into the radial gap because
$t^2/(t^2-\theta^2)\le9/8$ and $U\to\infty$.
Summing $e^{-c(U/d)(j^2-1)}$ gives a vanishing relative error.
The remote chart bound follows from
$|\sum(e^{iy_j}-1)|\le Q_2/2$ and the fixed diagonal gap.
Its $e^{-cUd}$ loss dominates the full reciprocal Gaussian
factor of logarithmic size $O(d\log U)$.

At the principal angles, the zero-sum Wick cancellation gives
$\|UQ_3\|_2=O(\sqrt{d/U})$, and Gaussian eighth moments give
$\|UQ_4\|_2=O(d/U)$. The real determinant ratio tends to one
because $d\theta^2\to0$. With the checked exponential moments,
Cauchy–Schwarz gives the claimed vanishing error, and the omitted
Gaussian ball has probability tending to zero. The complex
quadratic integral at $+\theta$ is

$$
I e^{Ud e^{i\theta}-i(d-1)\theta/2}.
$$

Its phase is $Ud\sin\theta-(d-1)\theta/2=k\pi$. Its
conjugate therefore has the same strict real sign, with no
phase approximation needed for either leading term.

## Fixed dimension and exhausted sequences

For fixed $d\ge3$, at every extremum of the real exponent
the sines are equal under the sum-angle constraint. Hence
all cosine magnitudes have a common value. A nonpositive
cosine bounds the sum by $d-2$, or all cosines are zero.
But $d\cos(\pi/d)\ge d-\pi^2/(2d)>d-2$.
At a maximum all cosines are then positive, and equal sines
force equal angles in the right semicircle. The constraint
selects the two largest diagonal cosines at $\pm\pi/d$.
The transverse complex gradient vanishes there too. Both
quadratic forms have positive real precision, so ordinary
fixed-dimensional complex Laplace expansion gives the same
leading pair. Compactness supplies a fixed real-exponent
gap off their neighborhoods.

At $d=2$, take $z_1=e^{it}$ and $z_2=-e^{-it}$, so
$\sum z_j=2i\sin t$. After shifting the angle the exact
normalized integral is $(2\pi)^{-1}\int e^{2iU\cos t}\,dt$
over one period. Its stationary points on the circle are
$0$ and $\pi$, with second derivatives of $2\cos t$ equal
to $-2$ and $2$. Stationary phase contributes
$e^{i(2U-\pi/4)}/(2\sqrt{\pi U})$ and its conjugate.
The resulting leading term is
$(\pi U)^{-1/2}\cos(2U-\pi/4)$. The prescribed $U$
gives $2U-\pi/4=k\pi$ exactly, so the signed value is
eventually positive in this dimension as well.

I also checked the two smaller-ratio regimes. When $d\ge8$
and $k\le d/4$, $k+3/8\le U\le k+5/8$ and the stated
outward ratios are at most $e^{-1}$, leaving $1-2/e>0$.
When $k/d\to\beta\in(0,\infty)$, each fixed signed offset
ratio converges to $e^{-j^2/(2\beta)}$. The first outward
ratios stay uniformly below one along the sequence, bounding
both tails by a summable geometric majorant. The limiting
alternating Gaussian sum is positive by the stated Jacobi
identity, or directly by Poisson summation.

If failing pairs occur at unbounded dimensions, a sequence
with $d\to\infty$ has a subsequence on which $k/d$ converges
in the compact extended interval $[0,\infty]$. The small,
finite positive, and infinite limits are exactly the three
checked regimes. Thus exceptional dimensions form a finite
set. Each fixed dimension has only finitely many exceptional
$k$ by the Laplace or stationary-phase result above, proving
the finiteness assertion.

**Signed** · quota_referee, independent agent-assisted mathematical review.
