# Positive Hankel blocks beyond exact moment agreement

Let $P_n(t)$ denote the long-cycle excedance polynomial divided by $t$, with fixed minimum cycle length $k\ge3$. Put

$$
D_n(x)=x^{n-2}\frac{P_n(1-1/x)}{P_n(1)},
\qquad
\frac{D_n(x)}{D_{n+1}(x)}=\sum_{j\ge0}\mu_jx^{-j-1}.
$$

**Theorem.** For every $k\ge150$ and $n\ge k$, the Hankel matrix $(\mu_{i+j})_{0\le i,j\le \lfloor7k/12\rfloor}$ is positive definite. This gives positive moment norms through polynomial degree $\lfloor7k/12\rfloor$, uniformly in the row size. Compared with the exact moment agreement through order $2\lceil k/2\rceil-1$, this adds linearly many Lanczos steps. The conclusion concerns the leading block of the moment functional. [Alexandersson’s consecutive interlacing conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances)

## The uniform complex perturbation

Define $\delta_n=[z^n]\exp(\sum_{j\ge k}z^j/j)$, the admissible-permutation fraction. Then $\delta_0=1$, $\delta_j=0$ for $0<j<k$, and $n\delta_n=\sum_{a=0}^{n-k}\delta_a$. For $n\ge k$ this recurrence gives $1/(2k)\le\delta_n\le1/k$. These bounds hold directly from $\delta_n=1/n$ for $k\le n<2k$. For higher $n$ the numerator lies between $1+(n-2k+1)/(2k)$ and $1+(n-2k+1)/k$ by induction.

Use $t=e^s$ and $h(s)=(e^s-1)/s$. The normalized cycle factor of length $j$ is $h(s)^j(1+g_j(s))$, where

$$
g_j(s)=\sum_{\ell\in\mathbb Z\setminus\lbrace 0\rbrace}
\left(\frac{s}{s+2\pi i\ell}\right)^j.
$$

This is the Eulerian pole-sum identity. The cycle EGF then gives

$$
\frac{P_n(e^s)}{P_n(1)}= e^{-s}h(s)^n G_n(s),\qquad
G_n(s)=
\frac{[z^n]\exp(\sum_{j\ge k}(1+g_j(s))z^j/j)}{\delta_n}.
$$

Since $0\le\delta_a\le1$ and $\delta_n\ge1/(2k)$, absolute coefficient majorization implies

$$
|G_n(s)-1|
\le 2k\left(\exp\left(\sum_{j\ge k}|g_j(s)|/j\right)-1\right).
$$

Center at $v=x-1/2$ and use the ellipse $v=(\xi+\xi^{-1})/4$, with $|\xi|=5$. In its exterior, taking the branch $|\xi|\ge5$ gives $s=\log(1-1/x)=-4\mathrm{atanh}(\xi^{-1})$. The geometric series after the first term gives $|s|\le4/5+(4/3)(1/5)^3/(1-1/25)<13/16$. For $b=149/1000$, using $\pi>157/50$ yields

$$
\frac{|s|}{2\pi-|s|}<b,
\qquad |g_j(s)|\le2\zeta(j)b^j\le(5/2)b^j.
$$

Indeed $|s+2\pi i\ell|\ge|\ell|(2\pi-|s|)$, and $\zeta(j)\le5/4$ for $j\ge3$ by an integral bound at exponent three. Thus $S=\sum_{j\ge k}|g_j|/j\le (50/17)b^k/k<1/100$. Using $e^S-1\le S/(1-S)$ gives $|G_n-1|<6b^k$. The quotient has no pole in the exterior. Its uniform-transform comparison is

$$
\frac{D_n(x)}{D_{n+1}(x)}=(-s)\frac{G_n(s)}{G_{n+1}(s)},
\qquad
\left|\frac{D_n(x)}{D_{n+1}(x)}-(-s)\right|<11b^k.
$$

The last bound uses $12/(1-6b^k)<13$ and $13|s|<11$.

## The centered Legendre estimate

Let $L$ be the Laurent coefficient functional of the quotient at infinity, so $L(x^j)=\mu_j$. The reference transform $-s$ is the Cauchy transform of uniform measure on $[0,1]$. In the centered variable its contour functional on $p(v)^2$, for real $p$ of degree at most $m$, differs from $L(p(v)^2)$ by at most

$$
11b^k\frac{13}{10}\max_{|\xi|=5}|p(v)|^2.
$$

Here Cauchy's coefficient formula applies by analyticity in the ellipse exterior, and ellipse length divided by $2\pi$ is at most $(5+1/5)/4=13/10$.

Let $\ell_j(v)=\sqrt{2j+1} \mathrm{P}_j(2v)$ be the orthonormal Legendre basis for $[-1/2,1/2]$. Write $c_i=\binom{2i}{i}/4^i$. The Legendre generating function factored at $2v=(\xi+\xi^{-1})/2$ gives

$$
\mathrm{P}_j(2v)=\sum_{i=0}^j c_i c_{j-i}\xi^{j-2i}.
$$

The Wallis product bound $c_i^2\le1/(2i+1)$ follows by bounding each squared product factor $((2a-1)/(2a))^2$ by $(2a-1)/(2a+1)$. Pairing terms $i$ and $j-i$, for $i\le j/2$ one has $\sqrt{2j+1} c_{j-i}\le\sqrt2$. When $j-2i\ge1$ the reflected term costs at most $1+1/25$ times the larger power. The central term costs at most that factor as well. Summing $\sum_i c_i25^{-i}=(1-1/25)^{-1/2}$ gives

$$
|\ell_j(v)|^2\le
\frac{2(1+1/25)^2}{1-1/25}\cdot 25^j.
$$

By Cauchy–Schwarz in the orthonormal basis and summing the geometric series in $j$, the Laurent functional satisfies

$$
\left| L(p(v)^2)-\int_{-1/2}^{1/2}p(v)^2\mathrm{d}v\right|
\lt 34\cdot 25^m b^k\int_{-1/2}^{1/2}p(v)^2\mathrm{d}v.
$$

For $m\le7k/12$, $25^m\le (5^{7/6})^k<(131/20)^k$. The rational test $34(19519/20000)^{150}<1$ proves the bound for all $k\ge150$. Translation is an invertible change of polynomial basis, so strict positivity applies to the Hankel matrix in the original variable.

## Localization of the finite Jacobi compression

For $k\ge750$ and $m\le\lfloor7k/12\rfloor$, the two localizing forms $L(xp^2)$ and $L((1-x)p^2)$ are also strictly positive for each nonzero real $p$ of degree at most $m$. On the real interval, $|\mathrm{P}_j(2v)|\le1$ follows from the Laurent expansion with $|\xi|=1$, since its coefficients sum to one. Thus $\sup_{0\le x\le1}|p(x)|^2\le(m+1)^2\int_0^1p(x)^2\mathrm{d}x$. An endpoint strip of width $\epsilon=1/[2(m+1)^2]$ contains at most half this mass. Off the left strip, $x\ge\epsilon$, and off the right strip, $1-x\ge\epsilon$. Each weighted integral is therefore at least $\int_0^1p(x)^2\mathrm{d}x/[4(m+1)^2]$.

On the ellipse, $|x|,|1-x|\le9/5$. The preceding contour perturbation is accordingly less than $62\cdot 25^m b^k\int_0^1p(x)^2\mathrm{d}x$ for either weighted form. The rational inequality $248(7k/12+1)^2(19519/20000)^k<1$ holds at $k=750$ and the upper bound decreases thereafter. This proves both localizing inequalities. On real polynomials of degree at most $m$, use the inner product $\langle p,q\rangle=L(pq)$ and define $A_m$ by $\langle A_m p,q\rangle=L(xpq)$. The localizing inequalities put the Rayleigh quotients of this finite self-adjoint operator strictly between zero and one. Its Jacobi matrix, in the orthonormal polynomial basis, therefore has spectrum in $(0,1)$. This matrix has size $m+1$, strictly below the degree $n-1$ of $D_{n+1}$ at the stated cutoff, including at $n=k$.

## The first potentially differing moment

Put $d=2\lceil k/2\rceil$. In the pole correction, contributions of the opposite nonzero poles cancel odd powers. Hence the first possible correction to $G_n$ occurs at degree $d$ in $s$. Define $c_d^*=2(-1)^{d/2}\zeta(d)/(2\pi)^d=-B_d/d!$. When $k$ is even the coefficient is $c_d^*\mathbb E_n[m_k]$. When $k$ is odd it is $c_d^*\mathbb E_n[m_{k+1}-k m_k]$. Here $m_j$ counts cycles of length $j$. This follows by expanding each denominator once at $s=0$ for the odd cycle length. Products of two corrections have higher order. Thus $\mu_j=1/(j+1)$ for $j<d$, and the change in $\mu_d$ is the difference of the two leading $G$ coefficients. The preceding agreement is consistent with the general long-cycle independence of excedance moments for constraint statistics. [Campion Loth et al., §7, Theorem 7.16](https://arxiv.org/pdf/2301.00898#page=21)

Distinguishing a cycle gives $\mathbb E_n[m_j]=\delta_{n-j}/(j\delta_n)$. For $n\ge2k-1$, in the even case $\mathbb E_n[m_k]\in[0,2/k]$. In the odd case the expression $\mathbb E_n[m_{k+1}-k m_k]$ lies in $[-2,0]$. To see the upper bound, use monotonicity of $a\delta_a$ from its recurrence and $a=n-k\ge k$ when the numerator can be nonzero. Then $\delta_{a-1}/(k+1)\le a\delta_a/((a-1)(k+1))\le\delta_a$. At $n=2k-1$ both terms vanish. Together these bounds give $|\mu_d-1/(d+1)|\le4\zeta(d)/(2\pi)^d<4^{-d}$ since $d\ge4$, $\pi>3$, and $5(2/3)^4<1$.

For the block with $m=d/2$, the only possible changed entry is the bottom-right one. In the uniform Gram matrix its Schur complement is the squared norm of the degree-$m$ monic shifted Legendre polynomial, namely $1/((d+1)\binom{d}{d/2}^2)$. The strict Wallis product bound makes this norm greater than $4^{-d}$. Hence that first extra block remains positive definite for every $k\ge3$ and $n\ge2k-1$.

## Exact replay and scope

Run the standard-library checker from this directory with Python 3.

~~~sh
python3 -IB verify_jacobi_moment_blocks.py
~~~

The checker verifies the rational constants for the analytic theorem and reconstructs 88 sample pairs by the cycle-length recurrence and exact Laurent division. It verifies the first potentially changed moment and the positive pivots in those sample pairs. The uniform statement follows from the contour bounds. [Independent mathematical review](review-jacobi-moment-blocks.md)

**Formal verification**　⬜ None. Full consecutive interlacing of the actual polynomials remains open.
