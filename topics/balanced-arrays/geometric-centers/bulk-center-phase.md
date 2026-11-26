# The compact bulk saddle and phase for all fixed caps

Fix integers $d\ge2$ and $1\le r\le d$. Let $a_{n,k}$ count labeled binary $n\times d$ arrays with every column sum $k$ and every row sum at most $r$, and let $P_n(q)=\sum_k a_{n,k}q^k$. The degree is $D_n=\lfloor nr/d\rfloor$: capacity is necessary, and allotting each column $k$ consecutive labels in the cyclic list of the $n$ rows realizes each quota $k\le D_n$. In the full-cap case the coefficients are exactly $\binom nk^d$.

Put $\phi=\pi/d$, $\zeta=e^{i\phi}$, $H(z)=\sum_{j=0}^r\binom dj z^j$, and $S(u)=H(u\zeta)$ for $u>0$. For an arbitrary compact subinterval of $(0,\infty)$, define

$$
\nu=(d-1)/2,\qquad
\theta(u)=\arg S(u),\qquad
\Psi_n(u)=n\theta(u)-\nu\arg\lambda(u),\qquad
C_n(u)=\frac{\sqrt d(2\pi n)^\nu|\lambda(u)|^\nu}{2|S(u)|^n},
$$

Here $\lambda$ is defined below and has positive real part. Uniformly on the compact interval,

$$
C_n(u)P_n(-u^d)=\cos\Psi_n(u)+O(n^{-1}).
$$

## Dominant saddles

For $|y_i|=1$ and $\prod_i y_i=-1$ put $R(u,y)=\sum_{j=0}^r u^j e_j(y)$. Normalized Haar integration on this torus gives

$$
P_n(-u^d)=\int_{\prod_i y_i=-1} R(u,y)^n\thinspace dy .
$$

A term survives exactly when its column exponents are all equal to $k$, at which time the surviving factor is $u^{dk}(-1)^k$.

For $d\ge3$ and $r<d$, the two-maximizer lemma of the [fixed-rank manuscript](../fixed-rank-eventual.tex) applies: the modulus is maximized exactly at the point with every coordinate equal to $\zeta$ and at its conjugate. Its proof compares diagonal points by the discrete sine bound, finds a diagonal point in every maximizing component by the affine dependence on a pair sum, and shows that each of the two preferred diagonal points is isolated by strict real quadratic curvature. In angles $y_i=\zeta e^{ip_i}$ with $\sum_i p_i=0$, the quadratic coefficient in $\log(R/S)$ is $-\lambda \sum_i p_i^2/2$, where, with $z=u\zeta$,

$$
\lambda(u)=\frac{zB(z)}{S(u)},\qquad B(z)=\sum_{\ell=0}^{r-1}\binom{d-2}{\ell}z^\ell .
$$

Indeed $\sum_{|I|=j}(\sum_{i\in I}p_i)^2=\binom{d-2}{j-1}\sum_i p_i^2$. The angles of the terms of $B$ lie in a sector of width strictly less than $\pi$, so $B(z)\ne0$. Replacing two diagonal angles by $\phi+p,\phi-p$, with $p=\pi$, leaves the product unchanged and replaces $S$ by $S-4zB(z)$. Maximality gives $\mathrm{Re}(zB(z)\overline S)\ge2|zB(z)|^2>0$.

For $d=2,r=1$, use $y_1=e^{i\alpha}$, $y_2=-e^{-i\alpha}$. Then $R=1+2iu\sin\alpha$ and its only two modulus maxima occur at $\alpha=\pm\pi/2$, precisely the two diagonal points. The same quadratic formula gives $\lambda=iu/(1+2iu)$, with $\mathrm{Re}\lambda=2u^2/(1+4u^2)>0$. This compact argument does not need a positive real part of the leading coefficient of $\lambda(u)$ as $u$ tends to zero.

For $r=d$, $R(u,y)=\prod_i(1+u y_i)$. Write $y_i=e^{i\alpha_i}$. The arithmetic-geometric mean inequality gives the Jensen bound

$$
|R(u,y)|^2
\le\left(1+u^2+\frac{2u}{d}\sum_i\cos\alpha_i\right)^d.
$$

When $d\ge3$, the constrained maximum of $\sum_i\cos\alpha_i$ is $d\cos\phi$, reached exactly at the common angles $\phi$ and $-\phi$. Indeed any stationary point on the compact torus has all sines equal, by varying one angle up and a second one down. If its cosines have mixed signs, they have common absolute value and their sum is at most $d-2$, which is strictly below $d\cos\phi$ by $1-\cos\phi\le\phi^2/2$ and $\pi^2<4d$. If there are no mixed signs the angles are all equal, including when all cosines are zero. Among common angles of product $-1$ the maximum is attained only by the two nearest ones. When $d=2$ the cosine sum is identically zero. Equality in the arithmetic-geometric mean bound requires equal cosines, hence both zero, which is again exactly the same two diagonal points. At these points the arithmetic-geometric mean bound is attained in every dimension.

For the full cap expand $\log(1+ze^{ip_i})$ at $p_i=0$ and sum; the first-order term cancels on $\sum_i p_i=0$. This gives

$$
\lambda(u)=\frac{z}{(1+z)^2},\qquad
\mathrm{Re}\lambda(u)=
\frac{u(1+u^2)\cos\phi+2u^2}{|1+u\zeta|^4}>0.
$$

This also agrees with the proper-cap formula interpreted with $B(z)=(1+z)^{d-2}$. No logarithm is needed at torus points where $R$ vanishes.

## Uniform integration

For either cap, $S$ never vanishes on the positive axis. For a proper cap its terms lie in the sector from $0$ to $r\phi<\pi$ and its argument is strictly interior. At the full cap $S=(1+u\zeta)^d$, so $\theta=d\arg(1+u\zeta)$ with $0<\theta<\pi$. Use this continuous principal argument, and use the principal argument of $\lambda$ in $(-\pi/2,\pi/2)$ for the Gaussian power. In the $d-1$ free angular coordinates the form $Q=\sum_i p_i^2$ has matrix $I+\mathbf1\mathbf1^\top$ of determinant $d$. Uniformly on a compact $u$-interval there is a fixed strict modulus gap off fixed neighborhoods of the saddles, and the real part of the logarithmic quadratic term is uniformly strictly negative definite in the displacement. Each result follows by compactness and the strict pointwise bounds above.

Choose small symmetric coordinate balls about the two saddles. The branch of $\log(R/S)$ near the first is the one vanishing at its center; it has expansion $-\lambda Q/2+T_3(p)+O(|p|^4)$ with homogeneous cubic $T_3$. Its real part and that of the quadratic are at most $-c|p|^2$ on the ball, uniformly. Taylor's formula for the exponential along the segment of the two exponents bounds the difference between $e^{n\log(R/S)}$ and $e^{-n\lambda Q/2}(1+nT_3)$ by

$$
O\left((n|p|^4+n^2|p|^6)e^{-cn|p|^2}\right).
$$

The cubic integrates to zero by oddness. The error integrates to $O(n^{-\nu-1})$, and completing the quadratic to the whole coordinate space gives leading term

$$
\frac{S(u)^n}{\sqrt d(2\pi n)^\nu\lambda(u)^\nu}
$$

for that saddle including normalized torus measure. The quadratic integral has the prescribed branch by analytic continuation in the right half-plane. The conjugate saddle contributes the conjugate term, and the remainder of the torus is exponentially smaller.
