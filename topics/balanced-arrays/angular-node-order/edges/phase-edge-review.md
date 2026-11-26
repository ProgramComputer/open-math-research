# Independent edge-sign review

I accept the all-dimension upper limiting sign in
[angular-upper-edge-sign.md](angular-upper-edge-sign.md) and the
actual-node upper transfer for each fixed dimension and cap in
[phase-edge-transfer.md](phase-edge-transfer.md). The lower limit in
the transfer note is also correct. Below I give an additional route
showing that only finitely many lower limiting signs can fail. It
does not identify a finite cutoff or certify the remaining signs.

## Upper sign and transfer

For $m=dj+s$ with $j\ge1$, the adjacent ratios in the low-$m$
case are strictly bounded above by $e^{-3/2}$ and $e^{-1/2}$,
respectively, in sum. In detail $m\ge d$ and $4m\le d^2$
force $d\ge4$, and $m+d\le d^2/2$ makes the right-hand log
ratio at most $2/d-(d+1)/d\le-1/2$. The other log ratio
is at most $-2(d-1)/d\le-3/2$. The subsequent ratios
decrease as the factorial blocks increase or decrease. Pairing
therefore works even when the left tail ends after its first term.
Since $e^{1/2}>3/2$, the sum of the first ratios is strictly below
$26/27$. In the second range the two roots at $\pm\pi/d$ really
have aligned sign $(-1)^j$. For $\beta=(2\ell+1)\pi/d\le\pi$,
the sine argument for $(\ell+1)\pi/d$ may lie beyond $\pi/2$,
but its supplement is at least $\ell\pi/d$, giving the stated
lower bound in both factors. A singleton angle at $\pi$ only reduces
the bound by the two-sided comparison. The remote sum is strictly
below $1/6$ of the principal magnitude because $e^2>7$. This
also treats $d=2$, where there are no other terms. Both proofs
cover equality in $4m=d^2$.

For the transfer, the finite monotonicity theorem eventually applies
since $n\ge d$ for fixed $d$. At the upper node and on a residue
class $nr=dD+s$, the difference from the upper endpoint phase is
exactly $\pi(j+s/d)>0$. At any fixed $w>0$, the phase divided by
$n$ tends to the argument of the radial row polynomial, which lies
strictly below $r\pi/d$. This proves $w\to\infty$. Expansion of
the radial phase and the angular precision gives
$n\rho/w\to\pi(j+s/d)/\sin(\pi/d)$, including $r=1$,
where the $r-1$ term is the empty set.

When $1\le r<d$, equality in the triangle bound for $e_r$ forces
all the coordinates equal by comparing two $r$-subsets differing
by a single element. On the compact chart complement the normalized
row modulus consequently stays below one by a fixed gap. After
the local rescaling the row expansion is dominated by a constant
times a fixed Gaussian because $n/w$ stays bounded. The Haar
covolume contributes the stated factor $1/\sqrt d$.
At a common odd angle $t$, the surviving phase from the leading
row term is $e^{inrt}=(-1)^D e^{ist}$. Multiplication by
$(-1)^{D-j}$ leaves $(-1)^j$. The exponential correction has
phase $e^{-it}$, so the root filter gives the stated
$(-1)^h$ at degree $s+dh$. The strictly positive normalized
limit implies the result on each of the finitely many attainable
residue classes, hence at every sufficiently large height.

At the lower node the transverse factor starts with a positive
real multiple of $w e^{i\theta}$, so the term subtracted from
the radial phase tends to $\nu\theta$, not zero. The expansion
of the radial phase gives $nw_k\to(\pi k+\nu\theta)/(d\sin\theta)$
as in the note. A first-moment bound on the overflowing rows for
each fixed quota $m$ costs $O(n^{-r})$, and the term bound
$((nw_k)^m/m!)^d$ allows the stated dominated limit.

## Positive lower signs for growing dimension

Write $U=U_{d,k}=(\theta/\sin\theta)(k+(d-1)/(2d))$ and
$F_d(q)=\sum_{m\ge0}q^m/(m!)^d$. I obtain
$(-1)^k F_d(-U^d)>0$ for all sufficiently large $d$, uniformly
over all integers $k\ge1$.

First suppose $d\ge8$ and $k\le d/4$. The sine inequality used
for the upper edge gives $1\le\theta/\sin\theta\le1+2/d^2$
directly from $1/(1-\theta^2/6)$. Consequently
$k+3/8\le U\le k+5/8$. The first left and right ratios are
$(k/U)^d$ and $(U/(k+1))^d$. Both are at most
$\exp(-3d/[8(k+1)])\le e^{-1}$ because $d/(k+1)\ge8/3$.
The strictly positive lower bound $1-2/e$ follows after normalizing
by the center term and pairing the two outward tails.

Next consider $d\to\infty$ with $k/d\to\beta\in(0,\infty)$.
Here $U=k+1/2+o(1)$. For each fixed signed integer $j$, the
magnitude of the term at $k+j$ divided by the term at $k$
tends to $e^{-j^2/(2\beta)}$. For $j>0$ this follows by
writing the ratio as $\prod_{i=1}^j(U/(k+i))^d$ and expanding
the logarithms. For $j<0$, use the corresponding falling factors
$(k-i)/U$, starting at $i=0$. Both first outward ratios tend to
$e^{-1/(2\beta)}<1$, and subsequent ratios are smaller. Therefore
the signed normalized sum tends to the strictly positive
Jacobi product
$\sum_{j\in\mathbb Z}(-1)^j e^{-j^2/(2\beta)}
=\prod_{m\ge1}(1-q^{2m})(1-q^{2m-1})^2$,
$q=e^{-1/(2\beta)}$.

Finally let $d\to\infty$ with $k/d\to\infty$, so $U/d\to\infty$.
On the determinant-minus-one torus, coefficient projection gives
the exact identity

$$
F_d(-U^d)=\int_{\prod z_j=-1}\exp\!\left(U\sum_j z_j\right)\,dz .
$$

Here exchange of the absolutely convergent exponential expansion
and Haar integration leaves only equal exponent vectors. Let
$D_z=\sum_j |z_j-\bar z|^2$ and let
$I=(2\pi U)^{-(d-1)/2}/\sqrt d$. On the complement of fixed
small transverse balls of radius $b$ at the odd common angles,
$D_z\ge b^2/3$. If $D_z<b^2/3$, principal angular offsets from
the circular mean have squared norm at most $3D_z$ by the
chord-angle comparison. Subtracting their mean gives a shorter
zero-sum lift in one of the balls.
Since $\Re\sum z_j\le |\sum z_j|\le d-D_z/2$,
split the chord penalty in half and integrate the second half
by the same relative-angle anchor argument. In detail for the
best anchor $\sum_{j\ne i}\arg(z_j/z_i)^2\le5D_z$, so the
integral is at most
$I\,d^{3/2}10^{(d-1)/2}\exp(Ud-Ub^2/12)$.
Dividing by $I e^{Ud\cos\theta}$ costs only
$\exp(Ud(1-\cos\theta))\le\exp(\pi^2 U/(2d))$.
Thus this ratio is $o(1)$ because $U/d\to\infty$.

For a chart at representative $t\in[-\pi,\pi]$ with
$|t|\le1/10$, Taylor expansion in the zero-sum column offsets gives

$$
U\sum_j e^{i(t+y_j)}
=Ud e^{it}-Ue^{it}Q_2/2+H,
\qquad H=-iUe^{it}Q_3/6+O(UQ_4).
$$

The constant is absolute on the fixed ball. With
$A=U\cos t$, use the real Gaussian of precision $A$ on the
zero-sum space. Young's inequality yields
$(\Re H)_+\le C A(Q_4+t^2 Q_2)$.
For any fixed multiplier, the first exponential expectation
on the ball is bounded by $C'\exp(C'd/A)$. To check this, write
$Y_j=(Z_j-\bar Z)/\sqrt A$ and impose $|\bar Z|\le1$
independently at cost at most two. It truncates $|Z_j|$ at
$2b\sqrt A$ for large $A$, and
$\sum (Z_j-\bar Z)^4\le8\sum(Z_j^4+1)$.
Choose the absolute ball radius small enough that the individual
exponent from $Z_j^4$ is at most $Z_j^2/4$. Then each factor of
the truncated expectation is at most $1+C'/A$ by the normal
quartic moment with exponential weight. For the $Q_2$ term,
the chi-square moment bounds its expectation by $\exp(C'dt^2)$
on a sufficiently small fixed angular interval, shrinking $1/10$
if necessary. Combining by Cauchy–Schwarz and including the
conversion from $A$ to $U$ proves

$$
|I_t|\le C I\exp(Ud\cos t+Cdt^2).
$$

Outside that fixed angular interval, each chart has a constant
diagonal gap in $\cos t$. Indeed
$|\sum(e^{iy_j}-1)|\le Q_2/2\le b^2/2$ by cancellation of
the linear term. Its integral is negligible even using total
Haar measure one, since $cUd$ beats $O(d\log U)$.
For near nonprincipal odd labels $|t|=j\theta$, $j\ge3$,
$\cos\theta-\cos t\ge c(t^2-\theta^2)$ by integration
of the sine on the near interval. The loss $Cdt^2$ can be
absorbed in half of $cUd(t^2-\theta^2)$. Summing the remaining
bound $C\exp[-c'(U/d)(j^2-1)]$ over nonprincipal odd labels
gives $o(1)$ relative to $I e^{Ud\cos\theta}$.

At $t=\theta$, the Gaussian $L^2$ norms of $UQ_3$ and
$UQ_4$ are $O(\sqrt{d/U})$ and $O(d/U)$ by the zero-sum
Wick identity and the normal eighth moment. The exponential
bound just established applies with multiplier two. Hence
Cauchy–Schwarz in $|e^H-1|\le |H|e^{(\Re H)_+}$ shows
that the error is $o(I e^{Ud\cos\theta})$. The omitted
Gaussian ball tail is $o(1)$ since $d/A\to0$.
Complex Gaussian integration now gives the principal contribution
$I\exp(Ud e^{i\theta}-i(d-1)\theta/2)$.
Its phase is exactly $k\pi$ by the definition of $U$.
The two principal terms therefore give the strict signed result.

If the all-$k$ claim at sufficiently large dimension failed, take
a sequence of increasing dimensions with a failing $k$. A
subsequence has $k/d$ tending to zero, to a positive finite
number, or to infinity. The three arguments exclude all these
possibilities.

For each fixed $d\ge3$, the same Poisson integral also gives
eventual positivity as $k\to\infty$. On the torus, any extremum
of $\sum\cos\theta_i$ has all $\sin\theta_i$ equal. If any
cosine is nonpositive then the sum is at most $d-2$, or is zero
when all cosines vanish. Since $d\cos(\pi/d)>d-2$ for $d\ge3$,
the global maxima have all cosines positive, hence all angles
equal, and occur exactly at $\pm\pi/d$. Ordinary fixed-dimensional
Laplace integration gives the same aligned principal pair as
above. When $d=2$, the integral reduces to the one-dimensional
phase $2U\cos t$ and fixed-dimensional stationary phase at its
two nondegenerate critical points gives
$(\pi U)^{-1/2}\cos(2U-\pi/4)+o(U^{-1/2})$.
Here $2U-\pi/4=k\pi$. Combined with the growing-dimension
argument, this proves that the exceptional set of lower signs
is finite. An explicit finite reduction or a direct all-parameter
inequality is still needed to conclude that there are no exceptions.

**Signed** · four_central, independent agent-assisted review of the upper sign and edge transfers, and author of the lower finiteness argument.
