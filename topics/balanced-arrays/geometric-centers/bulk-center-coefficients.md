# Local coefficient asymptotics at fixed dimension and cap

Fix integers $d\ge2$ and $1\le r\le d$. For $n$ labeled rows let $a_{n,k}$ count the binary arrays with all column sums $k$ and row sums at most $r$. Write

$$
H(w)=\sum_{s=0}^r\binom ds w^s,\qquad x=k/n.
$$

On any compact subinterval of $0<x<r/d$, let $w(x)>0$ solve $wH'(w)/(dH(w))=x$, and put $L(x)=\log H(w)-dx\log w$. The function $w$ is smooth because the derivative of the row-size mean with respect to $\log w$ is the strictly positive row-size variance. The limiting means as $w\downarrow0$ and $w\to\infty$ are $0$ and $r$, respectively.

Give each feasible row $A\subseteq[d]$ probability $w^{|A|}/H(w)$. Its incidence vector $X\in\lbrace 0,1\rbrace^d$ has mean $x\mathbf1$ by symmetry. Let $\Sigma(x)$ be its covariance matrix. Uniformly for lattice quotas in any such compact interval,

$$
\log a_{n,k}
=nL(x)-\frac d2\log(2\pi n)-\frac12\log\det\Sigma(x)
 +\frac{B(x)}n+O(n^{-3/2}),
\tag{1}
$$

where $B$ is smooth. The proof includes $r=1$ and $r=d$.

## Lattice inversion and the spectral gap

Put $Y=X-x\mathbf1$ and $\phi_x(\theta)=\mathbb E e^{i\theta\cdot Y}$. For $n$ independent rows, every counted array has probability $H(w)^{-n}w^{dk}$, so lattice Fourier inversion gives the exact identity

$$
a_{n,k}=e^{nL(x)}(2\pi)^{-d}
 \int_{[-\pi,\pi]^d}\phi_x(\theta)^n\thinspace d\theta .
\tag{2}
$$

Although the single centered characteristic function need not be periodic, the integrand in (2) is the integer-target lattice integrand because $nx=k$.

Every row distribution assigns positive mass to $0$ and to each coordinate vector $e_i$. If a real vector $t$ satisfies $t^\top\Sigma(x)t=0$, then $t\cdot X$ is constant on this support, forcing first that the constant is zero and then that $t_i=0$ for every $i$. Thus the covariance is positive definite, with its smallest eigenvalue bounded below uniformly on the compact $x$ interval. Likewise $|\phi_x(\theta)|=1$ requires $e^{i\theta\cdot X}$ to be constant on the support, since equality must hold in the triangle inequality for its expectation. Its value at $0$ fixes that constant to one and the singletons then give $\theta_i\in2\pi\mathbb Z$ for every $i$. The only such point in $[-\pi,\pi]^d$ is the origin. For every fixed positive distance from zero, compactness in $x$ and $\theta$ gives a modulus bound strictly below one.

## Expansion at the origin

Define the centered homogeneous cumulants

$$
\begin{aligned}
\kappa_{3,x}(s)&=\mathbb E(s\cdot Y)^3,\\
\kappa_{4,x}(s)&=\mathbb E(s\cdot Y)^4-3\bigl(s^\top\Sigma(x)s\bigr)^2,\\
C_{3,x}(s)&=-i\kappa_{3,x}(s)/6,\qquad
C_{4,x}(s)=\kappa_{4,x}(s)/24 .
\end{aligned}
$$

The support is finite and all moments vary smoothly in $x$. Choose a fixed ball about zero on which $|\phi_x(\theta)-1|<1/2$ uniformly. The analytic logarithm chosen to vanish at zero has uniformly bounded derivatives through order five on a smaller closed ball. Taylor expansion, or direct expansion of the characteristic function followed by $\log(1+z)$, gives there

$$
\log\phi_x(\theta)
=-\frac12\theta^\top\Sigma(x)\theta
 +C_{3,x}(\theta)+C_{4,x}(\theta)+O(|\theta|^5).
$$

The real quadratic term and the covariance lower bound imply $|\phi_x(\theta)|\le e^{-c|\theta|^2}$ on a sufficiently small fixed ball of radius $\eta$, for a uniform $c>0$.

Set $s=\sqrt n\thinspace \theta$. On $|s|\le n^{1/12}$ the exponent after removing its Gaussian term is

$$
n^{-1/2}C_{3,x}(s)+n^{-1}C_{4,x}(s)+O(n^{-3/2}|s|^5).
$$

Its magnitude is bounded uniformly and tends uniformly to zero on this region. Taylor expansion of the exponential through degree two, retaining the square of the cubic exponent and bounding the cross terms, gives

$$
\phi_x(s/\sqrt n)^n
=e^{-s^\top\Sigma(x)s/2}
 \left[
 1+n^{-1/2}C_{3,x}(s)
 +n^{-1}\left(C_{4,x}(s)+\frac12 C_{3,x}(s)^2\right)
 +O\left(n^{-3/2}(1+|s|^{15})\right)
 \right].
$$

For the stated remainder, the cubic Taylor bound on the exponential is a constant times the cube of the full non-Gaussian exponent. Each of these products is bounded by $n^{-3/2}$ times a polynomial of degree at most 15. The error from replacing the full exponent in its linear and quadratic Taylor terms by the displayed retained terms obeys the same bound.

On $n^{1/12}<|s|\le\eta\sqrt n$ the integrand is bounded by $e^{-c|s|^2}$, so the scaled integral there decreases faster than any inverse power of $n$. Outside the original $\eta$-ball the fixed torus gap makes the contribution exponentially small even after scaling by $n^{d/2}$. The Gaussian-polynomial integrals may also be extended to $\mathbb R^d$ at a faster-than-polynomial cost. The integral of the cubic term vanishes by oddness. Define

$$
B(x)=
\frac{\displaystyle\int_{\mathbb R^d}e^{-s^\top\Sigma(x)s/2}
 \left(C_{4,x}(s)+\tfrac12C_{3,x}(s)^2\right)\thinspace ds}
{\displaystyle\int_{\mathbb R^d}e^{-s^\top\Sigma(x)s/2}\thinspace ds}.
$$

Its smoothness follows by differentiating under the Gaussian integral on compact quota intervals. The integrands and all their fixed-order derivatives there have an integrable Gaussian-polynomial majorant. The leading integral is $(2\pi)^{d/2}/\sqrt{\det\Sigma(x)}$, bounded away from zero on compacts. Equation (2) is therefore the exponential factor times $(2\pi n)^{-d/2}(\det\Sigma(x))^{-1/2}[1+B(x)/n+O(n^{-3/2})]$. Taking the logarithm yields (1).

## Correction to the geometric node

Write $t_{n,k}=\sqrt{a_{n,k-1}/a_{n,k+1}}$ for the positive magnitude of the evaluation point in the original $q$ variable. For an index in a compact quota interval, use (1) for $x\pm1/n$ on a slightly larger compact interval. If $M(x)=\log\det\Sigma(x)$, the central difference yields

$$
\begin{aligned}
\frac1d\log t_{n,k}
&=\frac1{2d}\bigl(\log a_{n,k-1}-\log a_{n,k+1}\bigr)\\
&=-\frac1d L'(x)+\frac{M'(x)}{2dn}+O(n^{-3/2})\\
&=\log w(x)+\frac{(\log\det\Sigma(x))'}{2dn}+O(n^{-3/2}).
\end{aligned}
$$

The order $n^{-1}$ term involving $B$ contributes only $O(n^{-2})$, by smoothness. The same smoothness makes the central-difference remainders from the leading term and the determinant term $O(n^{-2})$ and $O(n^{-3})$, respectively. Finally $L'(x)=-d\log w(x)$ because the tilt equation cancels the $w'(x)$ terms. Both (1) and this node correction are uniform on fixed compact quota intervals.
