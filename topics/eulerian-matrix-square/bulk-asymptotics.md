# Limiting distribution of negative zeros of the Eulerian matrix square

Use the notation of the [endpoint result](endpoint-asymptotics.md). Thus $A_n(t)=\sum_{k=1}^n A(n,k)t^k$ is the shifted Eulerian row, and $xH_n(x)=\sum_{k=1}^n A(n,k)A_k(x)$ is the $n$th row polynomial of the ordinary square. For $a<b$ let $Z_n(a,b)$ be the number of distinct real zeros $-r$ of $H_n$ with $r>0$ and $a\le\log r\le b$.

**Theorem.** For all finite $a<b$,

$$
\lim_{n\to\infty}\frac{Z_n(a,b)}{n-1}
=\frac1\pi\left(\arctan\frac b\pi-\arctan\frac a\pi\right).
$$

Consequently $H_n$ has $n-o(n)$ simple negative zeros. The empirical distribution of the logarithms of the magnitudes of its negative roots converges to the Cauchy distribution with scale $\pi$. This count leaves an $o(n)$ remainder and the full real-rootedness conjecture open.

## Eulerian poles and a factorial-weighted row

For $t\ne0,1$ and $k\ge1$,

$$
\frac{A_k(t)}{k!}=\sum_{m\in\mathbb Z}\left(\frac{t-1}{\log t+2\pi i m}\right)^{k+1}.
\tag{1}
$$

Any logarithm of $t$ gives the same sum. To prove (1), put $\xi=(t-1)z-\log t$ in the shifted Eulerian generating function $(1-t)/(1-t e^{(1-t)z})$. It becomes $(1-t)/(1-e^{-\xi})$. The meromorphic function $f(\xi)=1/(1-e^{-\xi})$ has simple poles at $2\pi i m$ with residue $1$. Integrate $f(\xi)/(\xi+\log t)^{k+1}$ over the rectangles with real and imaginary boundaries at $\pm(2M+1)\pi$. The function $f$ is uniformly bounded on the boundaries, and the integrals tend to zero for $k\ge1$. The residue at $-\log t$ is the $k$th Taylor coefficient of $f$ there, so that coefficient is the negative of the sum of $1/(\log t+2\pi i m)^{k+1}$. Multiplying by $(1-t)(t-1)^k$ gives (1).

Define

$$
F_n(w)=\sum_{k=1}^n A(n,k)k! w^k=\int_0^\infty e^{-s} A_n(ws)\,ds.
\tag{2}
$$

We will use a uniform asymptotic for $F_n(w)$ when $w$ ranges over a fixed annular sector

$$
\mathcal W=\{w\in\mathbb C: m_0\le |w|\le M_0,\quad |\arg w|\le\pi-\varepsilon\},\qquad 0<m_0<M_0,\quad\varepsilon>0.
$$

Write $N=n+1$, $L=\log N$, and define, in a fixed sufficiently small complex neighborhood of $[1/2,2]$,

$$
\Phi_w(u)=-u+\log u+\log(1-(Nwu)^{-1})-\log(L+\log w+\log u).
\tag{3}
$$

Use the principal branches of these logarithms. The first logarithm of $u$ is near the real axis values of $\log u$, the argument of $\log(1-(Nwu)^{-1})$ is near $1$, and the argument of the final logarithm has positive real part for large $N$. Let $u_w$ be the unique solution of $\Phi_w'(u_w)=0$ in a fixed small disk about $1$, as verified below. Then, uniformly on $\mathcal W$,

$$
F_n(w)=n! N(Nw)^N e^{N\Phi_w(u_w)}
\left(\frac{2\pi}{-N\Phi_w''(u_w)}\right)^{1/2}(1+o(1)).
\tag{4}
$$

The square root uses the branch for which $(-\Phi_w''(u_w))^{1/2}$ is near $1$. In particular $F_n(w)$ has no zeros on $\mathcal W$ for sufficiently large $n$. We next prove (4), retaining control of the errors relative to the complex integral.

## Uniform estimates for the factorial-weighted row

For $s\in[N/2,2N]$, put $\lambda=\log(|w|s)$ and $\theta=\arg w$. The term of (1) with index $m=0$ is uniquely nearest in the logarithm denominator. For $m\ne0$,

$$
(\theta+2\pi m)^2-\theta^2\ge 4\pi\varepsilon m^2.
$$

Since $\lambda=L+O(1)$ on this interval, the ratio of the magnitudes of the $m$th and $0$th terms in (1) for $k=n$ is bounded by $(1+\gamma m^2/L^2)^{-N/2}$ for a fixed $\gamma>0$. The sum over $m\ne0$ is $O(e^{-cN/L^2})$ for some $c>0$. Indeed, extract $(1+\gamma/L^2)^{-(N-2)/2}$, then sum the remaining reciprocal quadratics, whose sum is $O(L)$. After $s=Nu$, the main term of the normalized integral $F_n(w)/(n!N(Nw)^N)$ on this interval is

$$
I_n(w)=\int_{1/2}^2 e^{N\Phi_w(u)}\,du.
$$

The error from the other poles in this integral is bounded by

$$
C e^{-cN/L^2}\exp\left(N\sup_{1/2\le u\le 2}\Re\Phi_w(u)\right).
\tag{5}
$$

For completeness, the entire part of the normalized integral with $s\notin[N/2,2N]$ is bounded in absolute value by $O(e^{-c_1N}e^{N(-1-\log L)})$ for some $c_1>0$. To see this, put $R=|w|$ and apply $|A_n(ws)|\le A_n(Rs)$. For $s\le\sqrt N$ the bound $A_n(Rs)\le n!\max(1,Rs)^n$ gives an exponentially smaller contribution than the claimed bound, uniformly in $R$. For $s\ge\sqrt N$, apply (1) to the positive number $Rs>1$. The pole sum divided by its $m=0$ term has absolute value at most $C(1+\log(Rs))$, by bounding the normalized terms by $(1+(2\pi m/\log(Rs))^2)^{-1}$. With $s=Nu$, after division by $(NR)^N$ the normalized integrand is bounded by

$$
C(1+\log(NRu))e^{N(-1-\log L)}
\left(u e^{1-u}\frac{L}{\log(NRu)}\right)^N.
\tag{6}
$$

The ratio $L/\log(NRu)$ is at most $3$ for $\sqrt N\le Nu\le N/10$. Hence the parenthesis is at most $(3/10)e^{9/10}<1$ there. On $1/10\le u\le 1/2$ the ratio is $1+O(1/L)$ and $u e^{1-u}\le e^{1/2}/2<1$. On $u\ge2$, the ratio is bounded above by $1+O(1/L)$ and $u e^{1-u}\le (2/e)e^{-(u-2)/2}$, by logarithmic differentiation. These strict bounds and integration of (6) give the exponential tail estimate.

On the complex neighborhood in (3), the function $\Phi_w(u)+\log L$ and its first three derivatives differ uniformly from those of $\log u-u$ by $O(1/L)$. Rouché’s theorem for the derivatives on a fixed small circle about $1$ gives the unique critical point $u_w$. Its equation $1/u_w-1=O(1/L)$ gives $u_w=1+O(1/L)$, and it depends continuously on $w$ by the implicit-function theorem. The derivative estimate can be sharpened in the angular direction. Directly from (3), $\Phi_w'-\Phi_R'=O(1/L^2)$ there for $R=|w|$, since $\log w-\log R$ is bounded and the remaining $w$-dependence in the derivative is $O(1/N)$. By reality and uniqueness, $u_R$ is real. Integrate $\Phi_w''=-1+O(1/L)$ along the segment from $u_R$ to $u_w$, on which $u=1+O(1/L)$. The equation $\Phi_w'(u_w)=\Phi_R'(u_R)=0$ then gives $u_w-u_R=O(1/L^2)$. Thus $\Im u_w=O(1/L^2)$.

Writing $v=\Re u_w$, we have $|\Phi_w(v)-\Phi_w(u_w)|=O(1/L^4)$ and $|\Phi_w'(v)|=O(1/L^2)$ by Taylor expansion around $u_w$. The real part of $\Phi_w''$ is bounded above by a negative constant on $[1/2,2]$. Hence the maximum of $\Re\Phi_w(u)$ on this real interval is at most $\Re\Phi_w(v)+O(1/L^4)$ by maximizing the quadratic upper bound around $v$. This proves

$$
\sup_{1/2\le u\le 2}\Re\Phi_w(u)\le \Re\Phi_w(u_w)+O(1/L^4),
\qquad \Phi_w(u_w)=-1-\log L+O(1/L).
\tag{7}
$$

Shift the path in $I_n(w)$ to the horizontal segment from $1/2+i\Im u_w$ to $2+i\Im u_w$. The connecting vertical segments give exponentially smaller terms than $e^{N\Re\Phi_w(u_w)}$, since $\log u-u$ has a strict real maximum at $1$ on the original interval and the endpoint real parts stay separated from the maximum. On the shifted segment let $u=u_w+t$ for real $t$. There $\Re\Phi_w''(u)$ is still bounded above by a negative constant, so the portion where $|t|>N^{-2/5}$ is exponentially small in $N^{1/5}$ relative to $e^{N\Re\Phi_w(u_w)}$. For $|t|\le N^{-2/5}$, the uniform bound on the third derivative gives

$$
e^{N\Phi_w(u_w+t)}=
e^{N\Phi_w(u_w)}\exp\left(\tfrac{N}{2}\Phi_w''(u_w)t^2\right)(1+O(N^{-1/5})).
$$

Integrate the Gaussian and extend it to the whole real line at exponentially small cost. The integral of its modulus and the modulus of its integral are both of order $N^{-1/2}$ because $-\Phi_w''(u_w)=1+O(1/L)$. The expansion therefore gives a relative $o(1)$ error in the claimed main term of (4). Equations (5) and (7) show that the other poles are also negligible relative to this complex Gaussian, since $e^{-cN/L^2+O(N/L^4)}\sqrt N\to0$. The off-interval tail is negligible by (7) and the exponential bound following (6). This completes the proof of (4).

## Negative real zeros from the phase

Fix a compact interval $r\in[r_0,r_1]\subset(0,\infty)$ and set

$$
w(r)=\frac{1+r}{-\log r+i\pi},\qquad
\theta(r)=\arg w(r)=-\frac\pi2-\arctan\frac{\log r}{\pi}.
$$

For $t=-r$ the two poles in (1) with the smallest logarithm denominators are the conjugate pair giving $w(r)$ and $\overline{w(r)}$. On the compact $r$ interval, the ratio of the magnitude of any other pole factor to $|w(r)|$ is at most a common $\delta<1$. The squared ratios are uniformly summable, since they are $O((|m|+1)^{-2})$. It follows that for $k\ge1$,

$$
\frac{A_k(-r)}{k!}=2\Re w(r)^{k+1}+O\big(|w(r)|^{k+1}\delta^{k-1}\big).
$$

Insert this in the row polynomial of the square. By positivity of the outer Eulerian coefficients, the total error in $-r H_n(-r)$ is $O(|w(r)|F_n(\delta|w(r)|))$. The points $w(r)$ and $\delta |w(r)|$ all lie in a single fixed sector $\mathcal W$ of the stipulated form. Equations (4) and (7) give

$$
\frac{F_n(\delta |w(r)|)}{|F_n(w(r))|}
=\delta^N\exp(O(N/L))\longrightarrow0
$$

uniformly in $r$. Thus

$$
-r H_n(-r)=2\Re\big(w(r)F_n(w(r))\big)+o\big(|w(r)F_n(w(r))|\big).
\tag{8}
$$

For large $n$, (4) gives a continuous real phase $\Theta_n(r)$ of the nonzero number $w(r)F_n(w(r))$. Namely, take the sum of $(N+1)\theta(r)$, $N\Im\Phi_{w(r)}(u_{w(r)})$, the argument of the Gaussian factor close to positive real, and the small argument of the factor $1+o(1)$. The choice is continuous because each factor in this exact quotient is continuous and the last factor remains in a disk about $1$. By (7), uniformly on the interval,

$$
\Theta_n(r)=(N+1)\theta(r)+O(N/L).
$$

The net decrease from $r_0$ to $r_1$ is $(N+1)(\theta(r_0)-\theta(r_1))+O(N/L)$. Between the endpoint values, each successive level in $\pi\mathbb Z$ can be sampled at increasing $r$ by taking the first hitting time after the preceding sample. At these points (8) gives alternating nonzero signs for $H_n(-r)$. The open intervals between these samples contain distinct negative roots. Therefore, with $r_0=e^a,r_1=e^b$,

$$
\liminf_{n\to\infty}\frac{Z_n(a,b)}{n-1}
\ge \frac{\theta(e^a)-\theta(e^b)}\pi
=\frac1\pi\left(\arctan\frac b\pi-\arctan\frac a\pi\right).
$$

Since the limiting mass of $[-M,M]$ tends to $1$ as $M\to\infty$, this proves the $n-o(n)$ count of distinct negative roots. The degree is $n-1$, so at most $o(n)$ of these roots can have multiplicity greater than one. The opposite interval bound follows by applying the same lower bound to the disjoint intervals $[-M,a-\eta]$ and $[b+\eta,M]$, subtracting their counts from $n-1$, and passing first to the limit in $n$, then letting $M\to\infty$ and $\eta\downarrow0$. This gives the stated limit and weak convergence. Counting with multiplicity gives the same limit because the excess multiplicity is $o(n)$.

## Prior work checked

The limiting measure agrees with the distribution already known for the individual Eulerian rows. Sobolev and Sirazhdinov used analytic methods in that setting, and Melotti gave a combinatorial proof. The argument above uses a second Eulerian pole expansion and a factorial integral to control the square. The literature and public project checks in the [endpoint note](endpoint-asymptotics.md), supplemented by the search for “Eulerian matrix square” with “zero distribution” and “Cauchy,” did not locate the square’s limiting distribution or a prior square analogue of the $n-o(n)$ negative-root count. [Sobolev](https://www.mathnet.ru/eng/dan/v235/i2/p277) · [Melotti, Theorem 1.1 and references](https://arxiv.org/pdf/2507.15908v2) · [Mao–Wang, Conjecture 4.1](https://arxiv.org/html/2607.01572v1)
