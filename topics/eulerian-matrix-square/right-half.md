# Eventual simple negative zeros in the closed unit disk

Let $A(n,k)$ count permutations of $[n]$ with $k-1$ descents, and let $xH_n(x)$ be the row polynomial of the ordinary square of the shifted Eulerian matrix. Then $H_n$ has degree $n-1$ and constant coefficient $n!$. [Mao–Wang, Conjecture 4.1](https://arxiv.org/html/2607.01572v1) · [Definitions and coefficient identities](endpoint-asymptotics.md)

**Theorem.** For all sufficiently large $n$, every zero of $H_n$ in $|x|\le1$ is simple and negative. Between any two consecutive zeros of either row $n$ or row $n+1$ lying in the closed unit disk, there is exactly one zero of the other row. The original row has in addition the simple zero at $0$.

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

## Consecutive alternation through the coefficient transition

For every fixed $K>0$, write $\alpha_{n,j}$ for the $j$th zero in increasing order of modulus. Then, simultaneously for $1\le j\le K\sqrt{n+1}$ and all sufficiently large $n$,

$$
\alpha_{n+1,j}>\alpha_{n,j}>\alpha_{n+1,j+1}.
$$

To see this, put $s_j=f(j)-f(j-1)$ and $B_j(k)=f(k)-f(j-1)-s_j(k-j+1)$. By concavity $B_j(k)\le0$ at all integers $k\ge0$, with equality exactly at $k=j-1,j$. For a real parameter $T$ tending to infinity, consider the normalized alternating sum

$$
S_{T,j}(d)=\sum_{k\ge0}(-1)^{k-j+1}\exp\big(TB_j(k)-d(k-j+1)\big).
$$

It is the coefficient model $\sum_{k\ge0}e^{Tf(k)}x^k$ evaluated at $x=-e^{-Ts_j-d}$ and divided by its signed term with $k=j-1$. The real variable $d$ stays in a fixed neighborhood of zero. The bounds used in (4) also apply here. For $k\le j-1$ and $k\ge j$ respectively, compare $B_j$ to the tangent remainder at $j-1$ and at $j$. The secant slope $s_j$ lies between the two tangent slopes, so $B_j(k)$ is bounded above by those remainders. Up to $k=2j+1$ this gives a uniform Gaussian majorant in the distance to $\{j-1,j\}$ when $j\le K\sqrt T$. Beyond that point the initial exponent is at most $-cT$ and $B_j'(k)\le -c/(1+j)$, giving an exponentially small geometric tail even in the infinite sum. These bounds apply after multiplication by any fixed power of $|k-j+1|$ and with $T/2$ in place of $T$.

With $l=k-j+1$ and $a=-Tf''(j-\tfrac12)/2$, the sum and its first derivative in $d$ are uniformly approximated by

$$
U_a(d)=\sum_{l\in\mathbb Z}(-1)^l e^{-a l(l-1)}e^{-l d}
$$

and its derivative, respectively. For $j<T^{2/5}$ only $l=0,1$ contribute up to $o(1)$, uniformly for bounded $d$, by the sharpened curvature bound as in (4). For $j\ge T^{2/5}$ and fixed $l$, expand around $j-\tfrac12$. Since the secant slope equals the derivative at its midpoint up to $O((1+j)^{-3})$, the remainder in the exponent compared to $-a l(l-1)$ is $O(T(|l|+1)^3/(1+j)^3)=o(1)$. The uniform tail bounds make this an approximation of the sum and derivative. By Jacobi's triple product with base $q=e^{-2a}$,

$$
U_a(0)=0,\qquad U_a'(0)=\prod_{m\ge1}(1-q^m)^3.
$$

In the product the factor $1-e^{-d}$ accounts for the zero at $d=0$. As $a\ge c_K>0$, the derivative has a uniform positive lower bound. The same Gaussian majorant bounds the second derivative for $d$ in a fixed compact interval. Thus $S_{T,j}(d)$ has a unique root $d_j(T)=o(1)$ near zero with derivative in $d$ uniformly bounded away from zero. [Jacobi's triple product](https://dlmf.nist.gov/17.8.E1)

It follows that $d_j(T)$ is differentiable in $T$. In the derivative of $S_{T,j}$ with respect to $T$, the inequality $|B|e^{TB}\le (C/T)e^{TB/2}$ for $B\le0$ gives $|\partial_T S_{T,j}|=O(1/T)$ by the same uniform tail bounds. Therefore $d_j'(T)=O(1/T)$. The model zero has logarithmic coordinate $Ts_j+d_j(T)$, which increases by $s_j+O(1/N)$ between $T=N$ and $T=N+1$.

For integer $N=n+1$, equations (2)–(3) actually give a relative error $O(e^{-c_K\sqrt N})$ for $p_{n,k}/(n!e^{N f(k)})-1$ throughout $k\le(K+1)\sqrt N$, by the explicit binomial bound. We may enlarge $K+1$ to any larger fixed constant, and take it bigger than $2K+2$. For the remaining coefficients the geometric tail just proved and the global bound in (3) give $O(e^{-cN})$ in the normalized sum. Hence the actual row's normalized value at $x=-e^{-Ns_j-d}$ differs from $S_{N,j}(d)$ by $O(e^{-c_K'\sqrt N})$ near $d_j(N)$. The derivative bound for the model and opposite signs on either side then give an actual root whose $d$ coordinate is $d_j(N)+O(e^{-c_K'\sqrt N})$. This root has modulus rank $j$, since $N(s_j-f'(j))$ and $N(f'(j-1)-s_j)$ are each bounded below by a positive constant by (1). Thus it lies between the counted circles $r_{j-1},r_j$.

The actual logarithmic coordinate of rank $j$ increases from row $n$ to row $n+1$ by $s_j+O(1/N)>0$, using $s_j\ge c/(1+j)$. The coordinate of rank $j$ in row $n$ exceeds that of rank $j+1$ in row $n+1$ by $N(s_j-s_{j+1})-s_{j+1}+o(1)>0$ for all $j\le K\sqrt N$. Indeed the first term is at least $cN/(1+j)^2$ by (1), whereas $s_{j+1}\to0$ for growing $j$, and the first term tends to infinity when $j$ is bounded. Since $x=-e^{-y}$ is increasing in $y$, these are the stated strict inequalities.

## Consecutive alternation in the moving annulus

For real $y\in[Y_0,\varepsilon\sqrt N]$, let $x=-e^{-y}$, $w=w_-(-y)$, $R=|w|$, and $\theta=\arg w=-\arctan(\pi/y)$. Write $\gamma_n(w)=F_{n+1}(w)/F_n(w)$ on the saddle sector. Its exact analytic logarithm obtained by subtracting the two saddle logarithms satisfies

$$
\frac{d}{d\zeta}\log\gamma_n(e^\zeta)=1+O(1/L),\qquad L=\log N,
\tag{12}
$$

uniformly on the smaller sector in (8). For this precision allow the saddle parameter $T$ in $T\Phi_{T,w}(u_{T,w})$ to vary from $N$ to $N+1$ as a real variable. The critical point equation gives the derivative in $T$ as $\Phi_{T,w}(u_{T,w})+(Twu_{T,w}-1)^{-1}-(\log T+\zeta+\log u_{T,w})^{-1}$. The derivative of the critical value in $\zeta$ was bounded by $O(1/L)$ in (8). The remaining two terms are also $O(1/L)$ on the enlarged sector, so Cauchy's estimate bounds their $\zeta$ derivatives the same way. Integrate for one unit of $T$. The Gaussian and error logarithms in each row have derivatives $O(1/L)$ as in (8), which proves (12). At positive $R$ the exact ratio is positive and its analytic logarithm is real. In particular

$$
\frac{\gamma_n(w)}{\gamma_n(R)}-1=i\theta+O(|\theta|/L+\theta^2).
\tag{13}
$$

Use the Eulerian pole sum to express $xH_n(x)=\sum_m w_m F_n(w_m)$, where the two principal $w_m$ are $w$ and $\bar w$. Subtraction of $\gamma_n(R)xH_n(x)$ from $xH_{n+1}(x)$ suppresses the omitted poles in this *difference* by an additional factor of order $1/y$. More precisely, the sum over omitted poles after subtraction, divided by $\gamma_n(R)|wF_n(w)|$, is $O(e^{-cN/y^2}/y)$. Here is the estimate. Index the omitted poles in pairs as in (9). For $m\le c_1 y$, with $c_1>0$ fixed small, their $\log w_m$ differ from $\log R$ by $O(m/y)$, and the whole joining segment lies in the smaller saddle sector of (8). This follows by substituting $w_m=(1+e^{-y})/(y\mp i(2m+1)\pi)$. By (12), $|\gamma_n(w_m)/\gamma_n(R)-1|\le C m/y$. For $k\ge n/2$, the proof of (9) bounds $\sum_{m\le c_1y}m r_m^{k+1}$ by $C e^{-cN/y^2}$, since the extra factor $m$ is summable against the Gaussian. For $k<n/2$ bound that sum by $O(y^2)$ and use the exponentially small estimate from (7). This bounds the near omitted poles after normalization, with the same-radius cost (6) absorbed in the exponential. For $m>c_1 y$, the magnitude ratio to the principal factor is at most a fixed $\delta_0<1$. The squared-ratio bound and the split at $k=n/2$ now give a relative $O(e^{-c'N})$ bound on the contribution of these poles in each row separately. Equation (12) bounds $|F_{n+1}(w)/F_n(w)|/\gamma_n(R)$ above and below by positive constants, so the far omitted poles are negligible also in the normalized difference.

At a negative root of row $n$, let $\psi_n=\Psi_n(-y)$, the phase of $wF_n(w)$. By (10), $\psi_n$ is within $O(e^{-cN/y^2})$ of a half-integer multiple of $\pi$. The subtraction above, (13), and conjugation give at that point

$$
\frac{xH_{n+1}(x)}{\gamma_n(R)|wF_n(w)|}
=-2\theta\sin\psi_n+O\left(|\theta|/L+\theta^2+e^{-cN/y^2}/y\right).
$$

Choose $Y_0$ sufficiently large and $\varepsilon$ sufficiently small. The error is then uniformly smaller than the main term, since $|\theta|\asymp 1/y$ and $|\sin\psi_n|$ is bounded away from zero. Thus row $n+1$ has alternating signs at the consecutive roots of row $n$ in the moving annulus. Indeed, consecutive roots there have successive phase levels. Every intervening grid level would have its own Rouché disk strictly between them, by (11) and the confinement estimates.

Moreover $\Psi_{n+1}-\Psi_n=O(1/y)$ on the real interval by (12) and the real logarithm at $R$. Between two such consecutive roots the range of $\Psi_{n+1}$ therefore has length at most $\pi+O(1/Y_0)+O(e^{-c/\varepsilon^2})$. Enlarging it by the uniform phase localization error still gives length less than $2\pi$. There can be at most two roots of row $n+1$ there, as each half-integer level has a unique root in its Rouché disk. The signs at the endpoints are opposite, and the intervening roots are simple, so exactly one occurs. The same reasoning with $\gamma_n^{-1}$ and the rows exchanged gives the reverse alternation. The corresponding principal contribution has opposite sign, and the same error estimates apply using the saddle normalization of row $n+1$.

This extends alternation from the fixed annulus and the circle-count region to the entire closed unit disk. For clarity, cover the logarithmic range by the fixed annulus $0\le y\le Y_0+2$, the moving annulus $Y_0\le y\le\varepsilon\sqrt N$, and the coefficient region of ranks through $K\sqrt N$ with $K>4/\varepsilon$. Each overlap contains at least two roots of each row for large $n$. For the first overlap this follows from the phase derivative in (11) and existence at each interior grid level. For the second take ranks near $(2/\varepsilon)\sqrt N$, whose logarithmic coordinates are asymptotic to $(\varepsilon/2)\sqrt N$ by the coefficient estimate. Thus any consecutive pair within the closed unit disk lies in one of the ranges that already has alternation in both directions. This proves the consecutive-row assertion.

## Prior work checked

Targeted searches on 25 November 2026 combined “Eulerian matrix square” and “Narayana transformation” with “unit disk,” “theta” and “simple negative.” Together with the [earlier screening](endpoint-asymptotics.md#prior-work-checked), these searches did not locate a previous result for the closed unit disk or the stated transition range.
