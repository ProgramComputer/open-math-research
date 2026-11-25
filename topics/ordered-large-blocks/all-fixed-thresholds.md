# Eventual interlacing at every fixed ordered block threshold

Fix $j\ge2$. Let $O_{n,j}(t)$ weight every ordered partition of $[n]$ by $t$ for each block of size at least $j$.

**Theorem.** For each fixed threshold $j$, every sufficiently large row $O_{n,j}$ has only simple negative zeros, and its zeros and those of the next row strictly interlace, with the next row's smallest root modulus strictly smaller. The threshold in $n$ can depend on $j$. This leaves the original all-size conjecture open in general. At $j=2,3$ the project has independent all-size proofs. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Two](threshold-two.md) · [Three](threshold-three.md)

The missing step between the two endpoint limits is a statement about the complex poles of the row generating function. At each argument $-q$ beyond the critical value $q>q_j^*$, precisely one conjugate pair has least modulus. We prove this for $j\ge4$ by a comparison of moduli on circles of radius at most one.

## The angular comparison

Set $E(z)=\sum_{s=0}^{j-1}z^s/s!$, $A(z)=2-E(z)$, $b(z)=j!z^{-j}(e^z-E(z))$ with its removable value at zero, and $H=A/b$. A pole at parameter $-q$ corresponds to $q=Q(z):=-j!H(z)/z^j$. Write $a=\pi/j$. For $0<r\le1$, the following two properties hold.

1. $|H(re^{i\theta})|$ increases strictly on $0\le\theta\le\pi/3$ and has strictly positive derivative in the interior.
2. Every $\pi/3\le\theta\le\pi$ gives a strictly larger modulus than every $0\le\varphi\le a$.

For the denominator, the coefficient of $z^m$ in $b$ is $d_m=j!/(j+m)!$. The cosine coefficients of $|b|^2$ at positive frequencies $k$ are $2B_k$, where $B_k=\sum_{m\ge0}d_m d_{m+k} r^{2m+k}$. They are positive. For $k\ge2$ one has $B_k/B_1\le (1/6)(1/7)^{k-2}$. Indeed the first successive ratio of coefficients is at most $1/(j+2)$ and all later ones are at most $1/(j+3)$. Since $|\sin(k\theta)|\le k\sin\theta$ on $0\le\theta\le\pi$, and $\sum_{k\ge2}(k^2/6)(1/7)^{k-2}=77/81<1$, differentiation shows that $|b|^2$ decreases strictly for $0<\theta<\pi$. Also $b$ never vanishes on the unit disk, since $|b(z)-1|\le\sum_{m\ge1}(1/(j+1))^m\le1/4$.

For the numerator, write $|A|^2=C_0-2\sum_{k=1}^{j-1}c_k\cos(k\theta)$ on this circle. The positive coefficients are
$$
 c_k=\frac{r^k}{k!}-
 \sum_{s=1}^{j-1-k}\frac{r^{2s+k}}{s!(s+k)!},\qquad
 (2-e^{1/(k+1)})\frac{r^k}{k!}\le c_k\le\frac{r^k}{k!}.
$$
Indeed the subtracted sum divided by $r^k/k!$ is at most $e^{1/(k+1)}-1$. In particular $c_1>0.35r$ and $c_2>0.30r^2$. On $0<\theta\le\pi/3$, we have $\sin(2\theta)\ge\sin\theta$ and $\sin(3\theta)\ge0$. The terms of $\sum k c_k\sin(k\theta)$ with $k\ge4$ cost at most $(2e-4.5)r^4\sin\theta<0.94r^4\sin\theta$. The first two give at least $(0.35r+0.60r^2)\sin\theta$, proving strict increase there. The decimal comparisons here follow, for example, by summing the exponential Taylor series through degree six and bounding its tail at $x\in[0,1]$ by $x^7/[7!(1-x/8)]$.

For $j\ge13$, $\theta\ge\pi/3$ gives $\sum c_k(1-\cos k\theta)\ge c_1/2>0.175r$. For $0\le\varphi\le a$ the corresponding sum is at most
$$
 \frac{\varphi^2}2\sum k^2c_k\le \frac{\varphi^2}2(r+r^2)e^r
 \le er\pi^2/169 < 0.175r .
$$
Thus these two angular regions have the required separation.

For $4\le j\le12$ a short rational certificate supplies the same comparison. Put $v=7/10$ for $j=4$ and $v=4/5$ otherwise. Then $1/2<v<\cos(\pi/j)$, using $\cos(\pi/4)=1/\sqrt2$ and $\cos(\pi/5)=(1+\sqrt5)/4$. With $T_k$ the Chebyshev polynomial, form
$$
 B(r,u)=\sum_{k=1}^{j-1}\frac{c_k}{r}\frac{T_k(v)-T_k(u)}{v-u}.
$$
Both divisions cancel polynomial factors. On $0\le r\le1$, $-1\le u\le1/2$, one has $B(r,u)>1/6$. The [standard-library verifier](code/verify_angular_modulus.py) expands $T_{k+1}=2uT_k-T_{k-1}$ and checks this bound in the bivariate Bernstein basis on the three $u$ intervals cut by $-1/2$ and $0$. More explicitly, after rescaling each rectangle to a unit square, a monomial $r^p y^q$ has coefficient $\binom{i}{p}\binom{h}{q}/(\binom{m}{p}\binom{d}{q})$ at Bernstein index $(i,h)$ of bidegree $(m,d)$. The basis is nonnegative and sums to one. All 27 rational minima exceed $1/6$. [Exact minima](results/angular-modulus.json)

Taking $u=\cos\theta$ proves $|A(re^{i\theta})|>|A(re^{i\arccos v})|$. The previous strict increase between zero and $\pi/3$ supplies the comparison with every $\varphi\le\pi/j$. Combining these numerator comparisons with strict decrease of the nonzero denominator proves properties 1 and 2.

## A single branch from the fold to infinity

For $0<\theta\le a$ the numerator has negative imaginary part for $r>0$, by the signs of $\sin(s\theta)$ for $1\le s<j$. The beta integral
$$
 b(z)=j\int_0^1 (1-u)^{j-1}e^{uz}\,du
$$
shows $0<\arg b(z)<\Im z$ in this sector, since $0<\Im z\le1$. Choose the continuous argument $V(r,\theta)=\arg A-\arg b$ starting at zero at $r=0$. By the polar Cauchy–Riemann equations,
$$
 \partial_r V=-r^{-1}\partial_\theta\log |H|<0.
$$
At $r=1$, $0<\theta<a$, the imaginary part of $(-A(e^{i\theta}))e^{-ij\theta}$ is
$$
 \sin(j\theta)-\sum_{s=1}^{j-1}\frac{\sin((j-s)\theta)}{s!}<0 .
$$
In fact concavity of the sine on $[0,\pi]$ bounds each summand's sine below by $(1-s/j)\sin(j\theta)$, and the sum of the weights $ (1-s/j)/s!$ is at least its $j=4$ value $25/24$. The arguments of $-A$ and $e^{ij\theta}$ both belong to $(0,\pi)$, so $\arg(-A)<j\theta$. Thus $V(1,\theta)<j\theta-\pi$.

For every $0<\theta<a$ there is exactly one $r(\theta)\in(0,1)$ with $V(r,\theta)=j\theta-\pi$. It depends analytically on $\theta$. At this point $q=Q(re^{i\theta})$ is positive real. Along the branch the Cauchy–Riemann equations and $V_r r'+V_\theta=j$ give
$$
 \frac{d\log q}{d\theta}
 =-V_r\left(r+\frac{(r')^2}{r}\right)>0 .
$$
They also imply $Q'(z)\ne0$ there, since $\partial_\theta\log|Q|=\partial_\theta\log|H|>0$.

At $\theta\downarrow0$ this curve is exactly the local upper branch leaving the isolated positive critical double pole. Indeed that local pole has $r<1$ by $\rho_j\le\rho_4<1$, lies in the sector, and satisfies the displayed argument equation by continuity from $\arg A=-\pi$, $\arg b=0$ and $j\theta=0$. Uniqueness in $r$ identifies it. At $\theta\uparrow a$ the radius tends to zero: a positive subsequential limiting radius would give $V(r,a)=0$, contradicted by $V_r<0$ and $V(0,a)=0$. Thus $q$ increases continuously from $q_j^*$ to $+\infty$. [Critical double pole and strict isolation](lower-spectral-edge.md) · [Local branches](fixed-threshold-inner-zeros.md)

At each such $q$ there can be no third pole of the same modulus as the constructed pair. Its value of $|H|$ would have to coincide at another angle in $[0,\pi]$, contrary to properties 1 and 2. The principal pair is the unique nearest pair just past $q_j^*$ by the critical gap. It continues to be the unique nearest pair throughout. Indeed the number of strictly smaller poles is locally constant: enclose the simple pair in disjoint small disks, and choose two nearby concentric circles isolating their common radius from all remaining poles. The argument principle preserves the counts under small changes of $q$, and no further equality of moduli occurs. This number begins at zero. Finally, in the convention $D_v=(1+q)^{-1}(A+q(e^z-E))$ with $v=1/(1+q)$, its derivative at a pole is $z^{j-1}/(j-1)!-2v$. For $0<\arg z<\pi/j$, this derivative has positive imaginary part. Its argument therefore connects $\pi/2$ at the fold to $(j-1)\pi/j$ at infinity without a full turn.

The [endpoint matching theorem](fixed-threshold-outer-interface.md) now applies. On a compact interval between the fold and infinity the nearest pair is uniformly isolated on a finite cover, so the other contributions are exponentially small. At the lower endpoint the fold estimate controls the errors relative to the vanishing phase shift. At the outer endpoint a circle with exactly $K$ exterior zeros matches the absolute phase count to the degree. The resulting signs account for every zero and give strict consecutive alternation. All arguments hold at each fixed $j\ge4$; the two smaller thresholds have all-size proofs. $\square$

## Distribution of the zeros

Let $m=\lfloor n/j\rfloor$ and write $F_n(q)$ for the fraction of zero moduli at most $q$, for the sufficiently large rows in the theorem. For every fixed $j\ge2$, the limiting distribution is zero for $q\le q_j^*$ and is
$$
 F(q)=\frac{j}{\pi}\arg z(q)\qquad(q>q_j^*),
$$
where $z(q)$ is the upper member of the nearest pole pair. The error $\sup_q|F_n(q)-F(q)|$ is $O_j(1/n)$. The distribution increases strictly from zero to one on $(q_j^*,\infty)$.

For $j\ge4$, put $\varphi(q)=\arg z(q)$. At each inner root $q_h$, indexed in increasing modulus, the matching theorem gives $h\pi<(n+1)\varphi(q_h)+\beta(q_h)<(h+1)\pi$ with $0<\beta<\pi$. Thus $|(n+1)\varphi(q_h)/\pi-h|<1$. Between consecutive such roots, strict increase of $\varphi$ bounds the counting discrepancy by two. The lower endpoint has phase angle zero. At the cut, $(n+1)\varphi/\pi=m-K+O(1)$, and as $q$ increases from the cut to infinity this expression increases to $(n+1)/j=m+O(1)$. Only $K$ roots remain there, with $K$ fixed for this threshold. The same upper bound by $O_j(1)$ applies between the last inner root and the cut. Below the critical value there are no roots. Division by $m$ proves the estimate. The [threshold-two](root-law.md) and [threshold-three](threshold-three-root-law.md) phase counts give the same bounded counting error at the two lower thresholds.
