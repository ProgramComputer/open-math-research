# Eventual real-rootedness at ordered threshold four

Let $O_n(t)=O_{n,4}(t)$ count ordered set partitions of $[n]$, weighted by $t$ for each block of size at least four. The degree is $\lfloor n/4\rfloor$, and the constant and leading coefficients are positive. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions)

**Theorem.** For all sufficiently large $n$, every root of $O_n$ is simple and negative. For all sufficiently large $n$, the moduli of the roots of $O_{n+1}$ strictly alternate with those of $O_n$, beginning with a smaller modulus of $O_{n+1}$ and ending with an extra larger modulus when the degree increases. The proof gives no explicit cutoff.

## Separation of the four low poles

Put $E_k(z)=\sum_{\ell=0}^k z^\ell/\ell!$, $C_4(z)=e^z-E_3(z)$, and $v=1/(1+q)$ for $t=-q$. The exponential generating function is $((1+q)D_v(z))^{-1}$ with

$$
D_v(z)=(1-v)e^z-E_3(z)+2v=C_4(z)+v(2-e^z).
\tag{1}
$$

Let $s=(12v)^{1/3}$ in the real function $J(s)=s+\log(1-s^3/12)-\log E_2(s)$, defined for $0\le s<12^{1/3}$. For $s>0$ its derivative has the sign of $2-E_3(s)$, since it equals $(s^2/4)(2/E_2(s)-1/(1-s^3/12))$. Hence it first increases from zero and then decreases to $-\infty$. Let $v_*$ correspond to its unique positive zero. We have $v_*<1/12$, since $J(1)<0$ is the elementary bound $e<30/11$. Work with $0<v<v_*$ and put $q_*=1/v_*-1$.

There are no real zeros in this range. For negative real $x$, $C_4(x)>0$ by the integral Taylor remainder, and $2-e^x>0$. For $x>0$, $e^x/E_2(x)$ is strictly increasing, so $D'_v(x)=(1-v)e^x-E_2(x)$ has one positive zero $x_c$. It is less than $(12v)^{1/3}$ because $J((12v)^{1/3})>0$. At its minimum $D_v(x_c)=2v-x_c^3/6>0$. There are no purely imaginary zeros either, since

$$
\Re D_v(iy)=\cos y-1+y^2/2+v(2-\cos y)>0
$$

for real $y$. At $v=v_*$ the only positive real zero is the double pole $s_*=(12v_*)^{1/3}$, where $D_{v_*}''(s_*)=s_*^2/2>0$.

We next show that no zeros cross the lines $\Im z=\pi$ or $\Im z=\pi/2$ as $v$ varies in $[0,1/12]$. For $z=x+i\pi$, the imaginary part of (1) would give $u^2=\pi^2/3-1$, where $u=x+1$. On this locus $\Re E_3(z)=1/3-u-4u^3/3$. For the positive choice $7/5<u<8/5$, this is less than $-4$, while the real exponential contribution is $-(1-v)e^x>-2$. For the negative choice $u<-7/5$, the real polynomial value is greater than $5$, while the real exponential contribution is negative and $2v\le1/6$. Both cases exclude a zero.

For $z=x+i\pi/2$, put $p=\pi^2/4$ and $u=x+1$. The real equation would give

$$
u^3-3(p-1)u+2-12v=0 .
$$

Using $31/10<\pi<16/5$ and $0\le v\le1/12$, this cubic has one root in each of $(-\infty,-2)$, $(0,3/5)$ and $(8/5,11/5)$. Indeed it is positive at $-2$ and $0$, negative at $3/5$ and $8/5$, and positive at $11/5$. The imaginary equation requires

$$
1-v=J_p(u):=e^{1-u}\frac{\pi}{2}\frac{u^2+c}{2},
\qquad c=1-p/3\in(11/75,1/4).
$$

On $u\le-2$ this is greater than one, by monotone decrease in $u$ and evaluation at $-2$. On $[0,3/5]$ its maximum is at an endpoint because the derivative has the sign of $2u-u^2-c$, which is increasing there. Both endpoint values are less than $11/12$, using $e<3$ and $e^{2/5}<3/2$. On $[8/5,11/5]$ the derivative's sign is decreasing, so the minimum is at an endpoint. Both endpoint values exceed one: use $e^{-3/5}>1/2$, $e^{-6/5}>2/7$, $\pi/2>3/2$ and $c>11/75$. This excludes a zero on the second line. Conjugation excludes the reflected lines. Each numerical exponential comparison here follows, for example, from the Taylor series with positive terms and a geometric bound on its tail.

At $v=0$ the only zero in either horizontal strip is the fourth-order zero at zero. In fact

$$
C_4(z)=\frac{z^4}{6}\int_0^1 (1-t)^3 e^{tz}\,dt,
$$

and the integral contains a strictly positive real part after rotation by $e^{-i\Im z/2}$ for $|\Im z|<\pi$. It is nonzero on the boundary too, since the rotated real integrand is strictly positive for $0<t<1$. Uniformly for $v\in[0,1/12]$, the exponential dominates as $\Re z\to+\infty$ in either strip, and the cubic dominates at the other end. The argument principle on sufficiently long rectangles therefore keeps the count of four in each strip. In particular every pole other than the four low ones satisfies $|\Im z|>\pi$.

On the circular boundary $|z|=2$ in the narrower strip, the same rotated integral and Jensen's inequality for the probability measure $4(1-t)^3\,dt$, of mean $1/5$, give

$$
|C_4(z)|\ge (\sqrt2/3)e^{x/5},\qquad |v(2-e^z)|\le \frac1{12}\sqrt{4+e^{2x}},\qquad x=\Re z.
$$

The first bound exceeds the second, as $4e^{-2x/5}+e^{8x/5}<32$ for $-2\le x\le2$. Convexity reduces this last inequality to its two endpoints, where one can use $e^{16/5}<28$ and $e^{4/5}<3$. Along the horizontal edges there are no zeros by the preceding test. Applying the argument principle to the disk intersected with the narrower strip gives that all four low poles satisfy $|z|<2$. These strict bounds hold up to $v=v_*$.

For small positive $v$ the four poles have arguments tending to $\pi/4,3\pi/4,-3\pi/4,-\pi/4$, by scaling (1) to $1+\xi^4$. Thus two stay on each side of the imaginary axis, since none can cross it. For $0<v<v_*$, they give one simple right pair $z,\bar z$ with $\Im z>0$, and one simple left pair $w,\bar w$ with $\Im w>0$. These are simple because a nonreal repeated zero and its conjugate in the same half-plane would exceed the count of two there. The labels are continuous and have the indicated limits at $v=0$; at $v=v_*$ the left pair stays simple and the right pair coalesces at $s_*$.

## A gap between the two pole moduli

Factor $D_v(t)=(t-z)(t-\bar z)(t-w)(t-\bar w)g(t)$. As in the [threshold-three argument](threshold-three.md#moduli-and-the-negative-real-pole), exponential interpolation expresses $g$ as $(1-v)$ times the simplex integral of

$$
\exp(\alpha z+\beta\bar z+\gamma w+\delta\bar w+\eta t),
\qquad \alpha+\beta+\gamma+\delta+\eta=1,
$$

with nonnegative barycentric coordinates and simplex measure of total mass $1/24$. For real $t$, averaging with the permutation of coordinates that conjugates the exponent gives a positive integrand, because the imaginary parts of all four nodes have absolute value less than $\pi/2$. Let $c_k=(\log g)^{(k)}(0)$ for $1\le k\le3$. These are respectively the mean, variance and third centered moment of $\eta$ in a probability measure, so

$$
0\le c_1\le1,\qquad 0\le c_2\le1/4,\qquad |c_3|\le c_2.
$$

Set $a=\Re(1/z)>0$, $b=-\Re(1/w)>0$, $U=|z|^{-2}$, $V=|w|^{-2}$, $d=a-b$, and $h=a+b$. Since $D_v(0)=v$ and each of the first three derivatives at zero is $-v$, the first three logarithmic derivatives of $D_v$ are $-1,-2,-6$. In the factorization these give

$$
d=\frac{1+c_1}{2},\qquad U+V=h^2+d^2-1-c_2/2,\qquad
4(a^3-b^3)-3aU+3bV=3/2+c_3/4.
$$

Consequently

$$
\frac32 h(U-V)=\frac32d(U+V)+3d-2d^3+\frac32d c_2-(3/2+c_3/4)
\ge\frac{U+V}{8}.
\tag{2}
$$

For the inequality, $d\in[1/2,1]$, $U+V\ge1/2$, and the concave function $(15/4)d-2d^3$ has minimum at least $13/8$ on this range. This bounds the right-hand side below by $1/16+(3/4)(U+V-1/2)$, which is at least $(U+V)/8$.

Thus $U>V$. With $\rho=|w|$ and $r=|z|/\rho$, we get $r\le e^{-\rho/36}$. If $r\le1/2$ this follows from $\rho<2$. Otherwise $U<4V$, hence $h\le\sqrt U+\sqrt V<3/\rho$. Equation (2) and $\tfrac12\log(U/V)\ge(U-V)/(U+V)$ then give $-\log r\ge\rho/36$.

Write $\varphi=\arg z$ and $\chi=\arg w$. We also have $\varphi<\pi/4$ and $\chi<3\pi/4$. For either upper pole $\zeta$, let $I(\zeta)=C_4(\zeta)/\zeta^4$. Its argument lies strictly between zero and $\Im\zeta$ by the positive integral, and $2-e^\zeta$ is below the real axis. Equation (1) implies

$$
4\arg\zeta+\arg I(\zeta)-\arg(2-e^\zeta)\ \in\ \pi+2\pi\mathbb Z .
$$

The expression is continuous and tends to $\pi$ for $z$ and $3\pi$ for $w$ as $v\to0$. Both extra terms are positive, proving the claims. In particular $\Im w\ge \rho/\sqrt2$, so $\Im z/\Im w\le\sqrt2\,\sin\varphi$.

All four nodes have imaginary parts uniformly bounded away from $\pm\pi/2$, by compactness and the strict strip bound also at $v=0,v_*$. Their real parts have absolute value at most $\rho$. Comparing the simplex integrals at $z$ and $w$, first compare the positive integrals of their moduli, at cost at most $e^{2\rho}$. At $w$ the argument of the integrand is at most $\max(\Im z,\Im w)$ in absolute value, so the cost for the complex integral is at most the secant of that angle. Its logarithm is at most $C\rho$: the angle is at most $\rho$ and stays away from $\pi/2$. Therefore

$$
\frac{|g(z)|}{|g(w)|}\le e^{C_1\rho}
$$

for a constant $C_1$ independent of $v$. Differentiating the factorization at $z,w$ cancels the two cross-pair distances in the derivative ratio, and gives

$$
\frac{|D'_v(z)|}{|D'_v(w)|}
=\frac{\Im z}{\Im w}\frac{|g(z)|}{|g(w)|}
\le \sqrt2\,\sin\varphi\, e^{C_1\rho}.
\tag{3}
$$

## Residues and signs on the inner part

At any pole $\zeta$ of (1), $D'_v(\zeta)=\zeta^3/6-2v$. In particular all poles outside the low strip are simple, and their derivative magnitudes are bounded below by a constant times $|\zeta|^3$. We record a uniform bound on their contribution. The integral for $g$ gives $g(0)$ bounded below by a positive constant, by bounded real parts and the uniformly positive cosine of the imaginary parts. For $L\ge4$, the bound $|D_v(t)|\le C(e^L+L^3)$ on $|t|=L$ and the factorization give $|g(t)|\le e^{C L}$ there. Jensen's formula then gives at most $C L$ zeros of $g$ in $|t|\le L$, uniformly in $v$. In particular the sum of $|\zeta|^{-3}$ over the distant poles is uniformly bounded, by summing dyadic annuli.

An exact residue sum for $O_n(-q)/n!$ is obtained by integrating $1/((1+q)t^{n+1}D_v(t))$ on squares with real and imaginary side coordinates $\pm 2\pi M$. On the right vertical side the exponential dominates and on the left the cubic dominates. On a horizontal side with $y=\Im t$, the imaginary part is $-y(1+x+x^2/2-y^2/6)$, $x=\Re t$. Where the parenthesis has modulus at least one, $|D_v(t)|\ge |y|$. Else $x+1$ is close to one of $\pm |y|/\sqrt3$. On the positive choice the exponential dominates the cubic and on the negative choice the cubic dominates. The integrals tend to zero, and the only poles besides the origin are the described zero set of $D_v$. The residue at the origin is the coefficient. Each other residue contributes with a minus sign.

For $N=n+1$ and $\Phi_n(q)=N\varphi+\arg D'_v(z)$, normalize the coefficient by $M_n=2/((1+q)|D'_v(z)|\,|z|^N)>0$. In these variables it equals $-\cos\Phi_n$ plus an error. The left pair contributes relative magnitude at most $\sqrt2\sin\varphi\,e^{C_1\rho}r^N$ by (3). The remaining error is at most

$$
C\sin\varphi\,(2/3)^N .
$$

Indeed $|D'_v(z)|\le C(\Im z)\rho^2\le C\sin\varphi\,\rho^3$ by differentiating the factorization, while the distant pole moduli exceed $\pi>3$ and their reciprocal cubes have uniformly bounded sum. Thus there is a fixed $K_0$ such that for all large $n$ and $N\rho\ge K_0$,

$$
\frac{O_n(-q)}{n!M_n(q)}=-\cos\Phi_n(q)+\epsilon_n(q),
\qquad |\epsilon_n(q)|\le\frac1{10}\sin\varphi.
\tag{4}
$$

The same bound holds for $n+1$ at those points.

Here $\arg D'_v(z)$ is the continuous argument in $(0,\pi)$: from $D'_v(z)=z^3/6-2v$ and $\varphi<\pi/4$, its imaginary part is positive. As $q\downarrow q_*$, the two right poles approach $s_*$. At that double pole $\partial_vD_v(s_*)=2-e^{s_*}<0$, since $C_4(s_*)>0$ and (1) vanishes. Also $D_{v_*}''(s_*)>0$. The resulting square-root expansion is $z-s_*=i\,c\sqrt{v_*-v}+O(v_*-v)$ with $c>0$, so $\arg D'_v(z)\to\pi/2$ and $\varphi\to0$.

## Matching the inner count to the outer ranks

Write $n=4m+s$, $0\le s<4$, and let $L_m=4!((6/5)m)^4$ be the scale in the [fixed-threshold outer theorem](fixed-threshold-outer-zeros.md). We will choose a boundary $q_n$ with exactly $K$ roots of larger modulus, where $K$ is fixed and sufficiently large. On $q_*\!<q\le q_n$, (4) will hold.

For the phase at large $q$, set $b_0=(24v)^{1/4}$ and scale $z=b_0\xi$. Uniformly near $\xi_0=e^{i\pi/4}$ the equation $D_v(b_0\xi)/v=0$ is

$$
1+\xi^4+b_0(-\xi+\xi^5/5)+O(b_0^2)=0.
$$

The simple root has $\xi=\xi_0+(3/10)b_0\xi_0^{-2}+O(b_0^2)$ by implicit differentiation. Thus

$$
\varphi=\frac\pi4-\frac{3b_0}{10\sqrt2}+O(b_0^2),\qquad
\arg D'_v(z)\longrightarrow\frac{3\pi}{4}.
$$

The same zeroth-order expansion at the left root gives $\rho/b_0\to1$. At $q=L_m/X^4$, uniformly for $X$ in fixed compact positive intervals, $b_0\sim X/((6/5)m)$, and it follows that

$$
\Phi_n(L_m/X^4)=(m+1+s/4)\pi-X/\sqrt2+o(1).
\tag{5}
$$

The section zeros in the outer theorem can be indexed here by a direct formula. For $Y=X/\sqrt2$, the root-of-unity filter gives

$$
X^s H_s(-X^4)=\frac12\left(e^Y\cos(Y-s\pi/4)+e^{-Y}\cos(Y-3s\pi/4)\right).
\tag{6}
$$

For $s=0$ the positive zeros in $Y$ are exactly $(i-1/2)\pi$, $i\ge1$. The strict section ordering puts the $i$th zero for any other residue $s$ between the consecutive $i$th and $(i+1)$st zeros for $s=0$. On that interval the first cosine has one zero at $(i-1/2+s/4)\pi$, a fixed positive distance from the endpoints. The exponentially small second term in (6) gives a zero tending to this point in translated coordinates, by opposite signs on either side. The indexed zero thus satisfies $Y_i=(i-1/2+s/4)\pi+o(1)$ as $i\to\infty$.

Choose a large fixed integer $K$. For all four residues, $X_s=\sqrt2(K+s/4)\pi$ is then strictly between the $K$th and $(K+1)$st zeros of $H_s(-X^4)$, with a fixed positive margin. Pick a short fixed interval containing $X_s$ whose closure remains in this gap. By (5), for large $n$ one can choose $X$ in the interval with $\Phi_n(L_m/X^4)=(m+1-K)\pi$. This uses continuity and the opposite deviations at the fixed endpoints. Put $q_n=L_m/X^4$ for such a choice. In the reciprocal polynomial normalized by the scale $L_m$, the corresponding circle has radius $X^4$. Local uniform convergence in the outer theorem and Rouché's theorem on the two fixed endpoint circles of the interval give exactly $K$ zeros in both disks and none in the closed annulus between them. These $K$ zeros are simple and negative by the individual small disks of that theorem. Thus there are precisely $K$ roots of $O_n$ with modulus exceeding $q_n$, and no root on the circle.

On $q_*\!<q\le q_n$ we have $v\ge 1/(1+q_n)$. Uniformly over $v\in(0,v_*)$, $\rho/v^{1/4}$ is bounded below by a positive constant, by the expansion at zero, positivity of $\rho$, and compactness away from zero. Therefore $N\rho\ge cK$ on this entire inner interval for large $n$. Choose the fixed $K$ large enough to ensure (4). The continuous phase starts at $\pi/2$ and ends at $(m+1-K)\pi$. First upper-level hits and the preceding last lower-level hits give $m-K$ ordered disjoint brackets with phases in $(j\pi,(j+1)\pi)$, $1\le j\le m-K$. There are opposite signs at each pair of endpoints by (4), so each bracket contains a root. Together with the $K$ exterior roots these exhaust the degree. All are therefore simple and negative, with $\sin\Phi_n$ of sign $(-1)^j$ at the inner root of rank $j$ in increasing modulus.

At any such inner root, $|\cos\Phi_n|\le\sin\varphi/10$ by (4). The next row has $\Phi_{n+1}=\Phi_n+\varphi$, and its error satisfies (4) at the same point. The term $\sin\Phi_n\sin\varphi$ dominates the change from $-\cos\Phi_n\cos\varphi$ and the other residues, whose total magnitude is at most $\sin\varphi/5$. Thus $O_{n+1}$ has sign $(-1)^j$ at each inner root when evaluated at its negative argument. At the last $K$ old ranks the same signs follow directly from the strict consecutive modulus order in the outer theorem, applied through rank $K+1$ to both rows. This order says exactly that the $j$th next-row root has smaller modulus than the $j$th old root, and the $(j+1)$st next-row root has larger modulus if it exists. Between the external and internal regions, the sign statement includes all old roots because their ranks exhaust the degree. The value at zero is positive. These signs force a next-row root before the first old root and one between every pair, plus the further root at large modulus when the degree increases. This completes the proof.

## Scope

The threshold-four theorem is eventual. The argument chooses a fixed $K$ by uniform residue bounds and then invokes local convergence of the outer polynomials for that $K$. An explicit cutoff would require quantitative choices for both stages to determine the length of a finite prefix. Targeted web and Firecrawl searches on 25 November 2026 combined ordered set partitions, blocks of size at least four, eventual real-rootedness and interlacing. These searches and the public status records did not locate a prior theorem for this exact eventual threshold. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Public investigation #108](https://github.com/1337isnot1337/solved-conjectures/issues/108)
