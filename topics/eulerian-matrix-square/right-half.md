# Eventual simple negative zeros in the closed unit disk

Let $A(n,k)$ count permutations of $[n]$ with $k-1$ descents, and let $xH_n(x)$ be the row polynomial of the ordinary square of the shifted Eulerian matrix. Then $H_n$ has degree $n-1$ and constant coefficient $n!$. [Mao–Wang, Conjecture 4.1](https://arxiv.org/html/2607.01572v1) · [Definitions and coefficient identities](endpoint-asymptotics.md)

**Theorem.** For all sufficiently large $n$, every zero of $H_n$ in $|x|\le1$ is simple and negative. The original row has in addition the simple zero at $0$.

The proof counts all complex zeros on the small-modulus side using coefficient estimates and the positive periodic Gaussian. In an overlapping range a two-pole analysis confines every zero to a disk containing exactly one negative root. The theorem concerns the closed unit disk. The moving range at $|x|>1$ and the all-row conjecture remain open in this investigation.

## Counting inside circles from the coefficients

Write $N=n+1$, $A_n(t)=\sum_{k=1}^n A(n,k)t^k$, and $p_{n,j}=[x^j]H_n(x)$. For $u\ge0$ define

$$
\rho(u)=\frac{u}{\log(1+u)},\qquad \rho(0)=1,\qquad f(u)=\log\rho(u).
$$

The function $f$ is smooth at zero, has $f'(u)>0$ and $f''(u)<0$, and there are absolute constants $c,C>0$ such that

$$
f'(u)\ge \frac{c}{1+u},\qquad -f''(u)\ge \frac{c}{(1+u)^2},\qquad |f'''(u)|\le \frac{C}{(1+u)^3}.
\tag{1}
$$

For strictness, $\rho(u)^{-1}=\int_0^1(1+su)^{-1}\,ds$. This integral is strictly decreasing, and the second derivative of its logarithm is the weighted mean of the strictly positive function $s^2/(1+su)^2$ plus the variance of $-s/(1+su)$ with the same weights. The bounds follow by continuity on compact intervals and differentiating $f(u)=\log u-\log\log(1+u)$ as $u\to\infty$. In particular, $u f'(u)\to1$ and $u^2 f''(u)\to-1$.

The Eulerian pole expansion from the [bulk proof](bulk-asymptotics.md#eulerian-poles-and-a-factorial-weighted-row) gives uniformly for integers $1\le t\le n$,

$$
\frac{A_n(t)}{n!}=\rho(t-1)^N\big(1+O(e^{-cN/(\log N)^2})\big).
\tag{2}
$$

For $t=1$ this is exact. For $t\ge2$, the nonprincipal terms relative to the principal term have total magnitude at most

$$
\sum_{m\ne0}\left(1+\frac{4\pi^2m^2}{(\log t)^2}\right)^{-N/2}.
$$

Extracting the $m=1$ factor with exponent $(N-2)/2$ and summing the remaining reciprocal quadratics proves (2), with the $O(1+\log N)$ factor absorbed into the exponential bound.

From $0\le e_{k,j}\le(j+1)^k$ and the alternating formula for $e_{k,j}$, we have

$$
0\le A_n(j+1)-p_{n,j}
\le\sum_{l=1}^j\binom{N}{l} A_n(j+1-l),\qquad 0\le j<n.
$$

The binomial bound uses $k+1\le N$ in the alternating formula. By (1), (2) and concavity, $A_n(j+1-l)/A_n(j+1)\le C\exp(-Nl f'(j))$. The binomial sum relative to $A_n(j+1)$ is therefore bounded by $C((1+e^{-Nf'(j)})^N-1)$. It tends uniformly to zero for $j\le K\sqrt N$ with any fixed $K>0$. Consequently

$$
p_{n,j}=(1+o(1))n! e^{N f(j)}\quad(0\le j\le K\sqrt N),\qquad
p_{n,j}\le C n! e^{N f(j)}\quad(0\le j<n).
\tag{3}
$$

Set $r_j=e^{-Nf'(j)}$, so $r_0<r_1<\cdots$. We claim that for fixed $K>0$ and all sufficiently large $n$, the circle $|x|=r_j$ contains no zero, and encloses exactly $j$ zeros with multiplicity, for every integer $0\le j\le K\sqrt N$. In fact, uniformly on those circles with $x=r_j e^{it}$,

$$
\frac{H_n(x)}{p_{n,j}x^j}
=\sum_{l\in\mathbb Z} e^{N f''(j)l^2/2}e^{ilt}+o(1).
\tag{4}
$$

To verify uniformity, bound each original term with $k=j+l$ by $C\exp(NG_j(k))$, where $G_j(k)=f(k)-f(j)-f'(j)(k-j)$. For $0\le k\le2j+1$, (1) gives $G_j(k)\le-c(k-j)^2/(2j+2)^2$. This supplies a summable Gaussian majorant independent of $n,j$ for $j\le K\sqrt N$. For $k>2j+1$, the exponent at $2j+1$ is at most $-c'N$, and concavity makes it decrease thereafter, so the total of these terms is $O(N e^{-c'N})$. The target series has the same type of uniform Gaussian majorant. For $j<N^{2/5}$ all the terms of either series besides $l=0$ tend to zero in total, by the sharpened bound $N/(2j+2)^2\to\infty$ in the Gaussian bound. For $j\ge N^{2/5}$ and bounded $l$, (1) gives

$$
NG_j(j+l)=N f''(j)l^2/2+O\big(N |l|^3/(1+j)^3\big),
$$

whose error tends uniformly to zero. Apply (3) with a slightly larger $K$ for those bounded offsets, and then use the Gaussian bounds for the remaining terms. This proves (4).

For $a>0$ the series in (4) with $a=-Nf''(j)/2$ equals

$$
\sqrt{\frac\pi a}\sum_{m\in\mathbb Z}\exp\left(-\frac{(t-2\pi m)^2}{4a}\right).
$$

This is the Fourier series of the periodic Gaussian, obtained by integrating the ordinary Gaussian Fourier transform over the real line. In particular the series is strictly positive. By (1), $a$ has a positive lower bound depending on $K$, and as $a\to\infty$ the original Fourier series tends uniformly to $1$. Hence its minimum over the allowed $a$ and $t$ has a positive lower bound. By (4), $H_n(x)/(p_{n,j}x^j)$ stays in the right half-plane on the circle. The argument principle gives the claimed root count. The annulus between each consecutive pair of circles contains exactly one zero with multiplicity. It is real by conjugation, simple by the count, and negative since $H_n$ is positive on $[0,\infty)$. Thus all zeros in $|x|\le r_{\lfloor K\sqrt N\rfloor}$ are simple negative.

## A two-pole estimate approaching zero

Let $z=-y+it$, $x=-e^z$, and let $w_\pm(z)=-(1+e^z)/(z\pm i\pi)$. Write $F_n(w)=\sum_k A(n,k)k!w^k$, and $T_\pm(z)=w_\pm(z)F_n(w_\pm(z))$. We prove confinement of every zero with $Y_0\le y\le\varepsilon\sqrt N$, $|t|\le\pi$, for a fixed sufficiently large $Y_0$ and a fixed sufficiently small $\varepsilon>0$. In estimates we allow a fixed margin of length $2$ on the real $y$ interval and take $|t|\le\pi+1$. There, $|w_\pm|\asymp 1/y$ and $|\arg w_\pm|=O(1/y)$ uniformly, so both $w_\pm$ lie in a sector away from the negative axis.

The [factorial saddle estimate](bulk-asymptotics.md#uniform-estimates-for-the-factorial-weighted-row) holds uniformly for

$$
c_* N^{-1/2}\le |w|\le C_*,\qquad |\arg w|\le 1,
\tag{5}
$$

with any fixed $c_*,C_*>0$. Put $L=\log N$ and $\lambda=\log(N|w|)$, so $\lambda\asymp L$. For clarity, the modifications needed in that estimate are as follows. The principal-pole ratio bounds hold with $\lambda$ in place of $L$, and the angles in (5) stay a fixed distance from the negative real axis. The critical point satisfies $u_w=1+O(1/\lambda)$ and $|u_w-u_R|=O(|\arg w|/\lambda^2)$ for $R=|w|$, by the angular derivative bound for the critical-point equation. This gives the same relative error bounds after comparison with the complex Gaussian. For the off-interval tails, split at $s=N^{3/4}$ in the factorial integral instead of $\sqrt N$. For $s\le N^{3/4}$ the bound $A_n(Rs)/n!\le\max(1,RN^{3/4})^n$ gives, after normalization by $(NR)^N$, a contribution bounded by $O(N^{-n/4})$. For $s\ge N^{3/4}$ put $s=Nu$. Then $\lambda/(\lambda+\log u)\le3$ for $N^{-1/4}\le u\le1/10$, since $\lambda\ge \frac12 L-O(1)$. On this interval $3u e^{1-u}\le (3/10)e^{9/10}<1$. On $[1/10,1/2]$ and $[2,\infty)$ the same exponential tail argument as in the bulk proof applies. This proves the uniform saddle estimate in (5). The local Gaussian Taylor bound in that proof gives relative error $O(N^{-1/5})$, which also bounds the exponentially damped outer poles and tails for large $N$.

We will need two consequences of the saddle estimate. First, at the same radius $R$ it gives

$$
\frac{F_n(R)}{|F_n(w)|}\le C\exp\left(CN(\arg w)^2/L^2\right).
\tag{6}
$$

To see this, evaluate the difference of the real parts of the saddle functions at the positive real critical point $u_R$. In the notation of the bulk estimate, the real part of $\log(1-(Nwu_R)^{-1})$ can only increase when the angle changes from zero. The loss from $-\log(L+\log w+\log u_R)$ is at most $C(\arg w)^2/L^2$. Shifting to $u_w$ changes the value by $O((\arg w)^2/L^4)$, by the critical-point equation and the displacement bound. The Gaussian factors are uniformly comparable. Also, the saddle gives the absolute lower bound

$$
|F_n(w)|\ge c n!\sqrt{N}(N|w|)^N\exp\left(N(-1-\log\lambda-O(1/\lambda))\right).
\tag{7}
$$

The second consequence is an estimate on logarithmic derivatives. For $w=e^\zeta$ in a slightly smaller sector than (5), the saddle formula gives an analytic logarithm of $wF_n(w)$ of the form

$$
\ell_n(\zeta)=C_n+(N+1)\zeta+Q_n(\zeta),\qquad Q_n', Q_n''=O(N/L),
\tag{8}
$$

with $C_n$ real and conjugation respected for $\zeta$ and $\bar\zeta$. In fact, $Q_n$ is the sum of $N$ times the critical value, the Gaussian logarithm, and the analytic logarithm of the factor $1+O(N^{-1/5})$. For the critical value its first derivative in $\zeta$ equals the partial derivative of $\Phi_w(u_w)$ because $\partial_u\Phi_w(u_w)=0$. This derivative is

$$
\frac1{Nwu_w-1}-\frac1{L+\zeta+\log u_w}=O(1/L).
$$

Apply Cauchy's derivative estimates in the $\zeta$ plane on fixed-radius disks inside an enlarged sector (5). This bounds the second derivative of the critical value and both derivatives of the Gaussian and error logarithms as required. The sector constants and $Y_0$ may be chosen to give a fixed margin around all $\zeta=\log w_\pm(z)$ used below.

In the Eulerian pole expansion for $A_k(x)$, keep the pair $w_\pm$. Let $R=\max(|w_-|,|w_+|)$ and let $w_*$ be a factor attaining this maximum. The omitted poles have ratios of moduli to $R$ bounded by numbers $r_m\le(1+c m^2/(1+y^2))^{-1/2}$, with at most two per integer $m\ge1$. Indeed their imaginary denominator parts are $t\pm(2m+1)\pi$, while the minimum of $|t-\pi|$ and $|t+\pi|$ is at most $\pi$ on $|t|\le\pi+1$. The differences of squared denominator parts are bounded below by a positive constant times $m^2$. In particular $\sum_m r_m^2=O(1+y)$. If $k\ge n/2$, the sum of the $(k+1)$st powers satisfies the sharper bound

$$
\sum_m r_m^{k+1}\le C e^{-cN/(1+y^2)}.
\tag{9}
$$

For $m\le1+y$ use $\log(1+c m^2/(1+y^2))\ge c' m^2/(1+y^2)$ and sum the resulting Gaussian, using $N/(1+y^2)\ge1$ for sufficiently small $\varepsilon$. For $m>1+y$, extract an $e^{-c'N}$ bound and sum the remaining squared ratios. This proves (9) even near a constant multiple of $\sqrt N$.

For the terms $k<n/2$, the squared ratio bound suffices. The contribution relative to $R|F_n(w_*)|$ is negligible, since

$$
\sum_{k<n/2} A(n,k) k! R^k\le n!(nR)^{n/2}
$$

and by (7) its ratio to $|F_n(w_*)|$ is $O(e^{-c N L})$, uniformly for the radii in question. For $k\ge n/2$, (9) gives a total absolute error at most $C R F_n(R) e^{-cN/(1+y^2)}$. By (6), $|\arg w_*|=O(1/y)$ makes the angular penalty smaller than the pole gap by a factor $O(L^{-2})$ in the exponent. Consequently

$$
xH_n(x)=T_-+T_++E_n(z),\qquad
|E_n(z)|\le C e^{-cN/y^2}(|T_-|+|T_+|).
\tag{10}
$$

This is an analytic identity with a uniform absolute error bound on the enlarged rectangle.

## Confinement and overlap

Write $\zeta_\pm(z)=\log w_\pm(z)$ in the branches from (5), and put

$$
\Psi_n(z)=\frac{\ell_n(\zeta_-(z))-\ell_n(\zeta_+(z))}{2i},\qquad
\theta(z)=\frac{\zeta_-(z)-\zeta_+(z)}{2i}.
$$

These are real on the real line. Direct differentiation gives $\theta'(z)=-\pi/(z^2+\pi^2)$, $\zeta_\pm'=O(1/y)$, and $\zeta_--\zeta_+=O(1/y)$. By (8), the difference of the derivatives of $Q_n(\zeta_\pm(z))$ is $O(N/(Ly^2))$. To see this, split the difference into $Q_n'(\zeta_-)(\zeta_-'-\zeta_+')$ and $(Q_n'(\zeta_-)-Q_n'(\zeta_+))\zeta_+'$, and apply both bounds in (8). Thus on the enlarged rectangle

$$
\Re\Psi_n'(z)\le -c_0 N/y^2,\qquad |\Psi_n'(z)|\le C_0 N/y^2.
\tag{11}
$$

Here $Y_0$ is large enough that $\Re\theta'(z)$ is bounded above by a negative constant times $1/y^2$ for the bounded imaginary parts being used. The use of the logarithmic derivative difference provides the same $y^{-2}$ scale for the error.

Divide (10) by the nonvanishing analytic factor $\exp((\ell_n(\zeta_-)+\ell_n(\zeta_+))/2)$. The resulting function is $2\cos\Psi_n(z)$ plus an error bounded by $C e^{-cN/y^2+|\Im\Psi_n|}$. At a zero, the identity $|\cos(a+ib)|^2=\cos^2 a+\sinh^2 b$ first gives $|\Im\Psi_n|=O(e^{-cN/y^2})$ by bounding $|\sinh b|e^{-|b|}=(1-e^{-2|b|})/2$. This argument uses $\varepsilon$ sufficiently small to make the error uniformly small. The real phase is then within $O(e^{-cN/y^2})$ of a level $(j+1/2)\pi$. Integration on the vertical segment in (11) gives $|\Im z|=O((y^2/N)e^{-cN/y^2})$, so the phase at $\Re z$ is also within $O(e^{-cN/y^2})$ of that level. The derivative bound on the real axis and the fixed margins give a unique real preimage $z_j$, at distance $O((y^2/N)e^{-cN/y^2})$ from $z$. This follows by the intermediate value theorem on each side of $\Re z$ using intervals of length a sufficiently large constant times $(y^2/N)e^{-cN/y^2}$.

Put $y_j=-z_j$. Around $z_j$ choose a circle of radius $a y_j^2/N$ for a fixed sufficiently small $a>0$. On this disk $y\asymp y_j$, and (11), integrated along a segment from the center, bounds the phase distance from the central level between positive constants on the boundary, with upper bound less than $1/4$. In fact the lower bound follows from the real-part derivative bound averaged along the segment, after taking absolute values of the complex displacement. The cosine has exactly one simple zero in the disk by the same lower bound and the upper bound excluding the adjacent levels. The relative perturbation on its boundary is uniformly smaller than the modulus of the cosine by (10) and sufficiently small $\varepsilon$. Rouché's theorem gives exactly one zero with multiplicity in the disk. Conjugation forces it to be real in $z$, and its image in $x$ is simple negative. Every possible zero over $Y_0\le y\le\varepsilon\sqrt N$ lies in such a disk by the localization estimate and the choice of $\varepsilon$. The fixed annulus $0\le y\le Y_0$ is covered by the [fixed-annulus theorem](compact-annuli.md). It follows that every zero in $e^{-\varepsilon\sqrt N}\le |x|\le1$ is simple and negative.

Finally choose fixed $K>2/\varepsilon$ and $J=\lfloor K\sqrt N\rfloor$. Since $u f'(u)\to1$, $N f'(J)\sim\sqrt N/K$ and $r_J\ge e^{-\varepsilon\sqrt N}$ for all sufficiently large $n$. The circles counted in (4) therefore cover the remaining part of the closed unit disk and overlap the two-pole region. This completes the proof.


## Prior work checked

Targeted searches on 25 November 2026 combined “Eulerian matrix square” and “Narayana transformation” with “unit disk,” “theta” and “simple negative.” Together with the [earlier screening](endpoint-asymptotics.md#prior-work-checked), these searches did not locate a previous result for the closed unit disk or the stated transition range.
