# Where the geometric-center sign test fails

Fix $d\ge2$ and $1\le r\le d$. Let $a_k$ count the labeled binary $n\times d$ arrays with common column sum $k$ and each row sum at most $r$. Put $P_n(q)=\sum_k a_k q^k$, $D_n=\lfloor nr/d\rfloor$ and $t_k=(a_{k-1}/a_{k+1})^{1/2}$ for $1\le k<D_n$. A successful geometric center has $(-1)^kP_n(-t_k)>0$. Success at every center is a sufficient test for simple negative zeros. The [logarithmic dimension theorem](../dense-regime/README.md) uses that test uniformly under its hypotheses.

**Theorem.** Fix any interval $[a,b]$ of positive length in $(0,r/d)$. Among internal indices with $a\le k/n\le b$, the proportions with $(-1)^kP_n(-t_k)>0$ and with $(-1)^kP_n(-t_k)<0$ each tend to $1/2$ as $n\to\infty$. The proportion giving zero tends to zero. The same three limits hold among all internal indices. Every dimension and cap in this theorem is fixed before taking the limit. Thus even in a family known to have only real zeros, the centers can give the wrong sign on half of the actual row.

## The local phase at the geometric center

Set $\phi=\pi/d$, $\zeta=e^{i\phi}$ and $H(z)=\sum_{s=0}^r\binom ds z^s$. Let $w(x)>0$ solve $wH'(w)/(dH(w))=x$. Under the row tilt proportional to $w^{|S|}$ on labeled subsets of size at most $r$, the row incidence vector has positive definite covariance $\Sigma(x)$. Positivity follows from the empty and singleton row types. The derivative of its total mean in $\log w$ is its positive variance, so $w$ is analytic in the open interval. Write $\theta(u)=\arg H(u\zeta)$, choosing the branch that vanishes at zero, and $f(x)=\theta(w(x))$.

The [coefficient estimate](bulk-center-coefficients.md) on any compact interior interval gives

$$
\log(t_k^{1/d})=\log w(x)+h(x)/n+O(n^{-3/2}),\qquad
h(x)=\frac{1}{2d}\frac{d}{dx}\log\det\Sigma(x),\qquad x=k/n.
$$

A first-order local limit alone would allow an uncontrolled change to the phase when multiplied by $n$. The estimate retains the determinant correction and gives an error smaller than $1/n$.

The [two-saddle estimate](bulk-center-phase.md) on compact positive $u$ intervals gives, after division by a strictly positive factor,

$$
P_n(-u^d)\ /\ A_n(u)=\cos(n\theta(u)+\chi(u))+o(1).
$$

Here $\chi(u)$ is a smooth choice of the Gaussian phase; the error is uniform. In particular, setting $u=t_k^{1/d}$ and multiplying by $(-1)^k$ gives the sign of a real number of the form

$$
\cos\left(nF(k/n)+\psi(k/n)\right)+o(1),\qquad
F(x)=f(x)-\pi x,\qquad
\psi(x)=h(x)w(x)\theta'(w(x))+\chi(w(x)).
$$

The smoothness on compact intervals makes the replacement uniform. The function $f$ is real analytic, and it is nonlinear. Indeed $f(0+)=0$, $f(r/d-)=r\pi/d$, and $f'(0+)=d\sin(\pi/d)<\pi$. The leading power of $H$ gives the upper limit of the phase, since all its terms on the ray have arguments between zero and $r\pi/d$. For $r=d$, use $H(z)=(1+z)^d$ and the continuous argument. Near zero, $x=w+O(w^2)$ and $\theta(w)=d\sin(\pi/d)w+O(w^2)$. Thus the endpoint secant has slope $\pi$ while the initial derivative differs. In particular $F'$ is nonconstant on every positive-length interior interval.

## Uniform distribution of the sampled phase

For each nonzero integer $m$, consider the exponential sum of $\exp(im[nF(k/n)+\psi(k/n)])$ over $a\le k/n\le b$. On $[a,b]$ there are only finitely many points where $mF'(x)$ is an integer multiple of $2\pi$. Indeed $F'$ is bounded there, is analytic in a neighborhood, and is nonconstant. Remove intervals around those finitely many points whose total length is at most $\epsilon$. Elsewhere $|1-\exp(imF'(x))|$ is bounded below by a positive constant depending on the removed intervals.

Divide each remaining interval of indices into blocks of $L=\lfloor n^{1/3}\rfloor$ consecutive terms, with shorter blocks at the ends. In a block beginning at $k_0$, put $x_0=k_0/n$ and $k=k_0+j$. Bounded derivatives give

$$
nF(x_0+j/n)+\psi(x_0+j/n)
=nF(x_0)+\psi(x_0)+jF'(x_0)+O(L^2/n+L/n).
$$

The geometric progression formed by the linear terms has bounded sum on each block. The change in the exponential caused by the error is $O_m(L^2/n+L/n)$ per term. After division by the number of indices, which is $n(b-a)+O(1)$, the sum on the retained intervals tends to zero; the removed intervals contribute at most $\epsilon/(b-a)+o(1)$. Letting $\epsilon$ decrease to zero proves the exponential-sum limit for every $m\ne0$. The Fourier criterion for equidistribution now gives uniform distribution of the angles modulo $2\pi$. Equivalently one may approximate continuous periodic functions by trigonometric polynomials and then approximate interval indicators from above and below.

The positive and negative cosine sets both have normalized length $1/2$. Since the approximation error tends uniformly to zero, eventual sign disagreements with this cosine can occur only where its absolute value is smaller than an arbitrarily prescribed positive tolerance. The measure of these arcs tends to zero with the tolerance. This proves the three limits on $[a,b]$. The omitted fraction outside $[\epsilon,r/d-\epsilon]$ is at most $2\epsilon d/r+o(1)$, which proves the assertion for all internal nodes.

The conclusion concerns a sufficient sign test. A reversed sign is compatible with real-rootedness. In particular at $d=r=2$ the polynomials have only negative roots for every positive $n$, even though the test has limiting success proportion $1/2$.
