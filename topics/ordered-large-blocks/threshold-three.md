# Ordered set partitions counted by blocks of size at least three

Let $O_n(t)=O_{n,3}(t)$ count ordered set partitions of $[n]$, with weight $t$ for each block of size at least three. The constant and leading coefficients are positive, and the degree is $\lfloor n/3\rfloor$. [Alexandersson's conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions)

**Theorem.** For every $n\ge0$ all zeros of $O_n$ are simple and negative, and consecutive rows strictly interlace wherever there are roots to compare. In positive moduli, the $j$th root of row $n+1$ is smaller than the $j$th root of row $n$, which is smaller than the $(j+1)$st root of row $n+1$ whenever that root exists.

The analytic proof starts at $n=94$. The finite verification checks rows $0\le n\le94$ and consecutive pairs beginning at $0\le n\le93$.

## Poles

Put $v=1/(1+q)$ for $t=-q<0$. The row exponential generating function is $1/((1+q)D_v(z))$, where

$$
D_v(z)=(1-v)e^z-1-z-z^2/2+2v.
\tag{1}
$$

Let $v_*$ be the unique positive zero in $(0,1)$ of $2\sqrt v-\log(1+2\sqrt v)+\log(1-v)$. In the variable $b=\sqrt v$ the expression starts at zero, tends to $-\infty$ at one, and its derivative has the sign of $1-2b-2b^2$ for $b>0$. Also $v_*<1/3$, since $23/20<2/\sqrt3<7/6$ and $e^{7/6}<129/40=(3/2)(1+23/20)$. The exponential bound follows by summing through degree seven and bounding the remaining tail by $(7/6)^8/(8!\,(1-7/54))$. We use $0<v<v_*$, or $q>q_*:=1/v_*-1$.

There is one real negative pole $-R$: $D_v(-r)$ starts at $v>0$, is strictly concave for $r\ge0$, and tends to $-\infty$. Its derivative in $r$ is negative at $R$. Also $R<9/5$ because $D_v(-9/5)$ increases with $v$ and at $v=1/3$ is $(2/3)e^{-9/5}-23/150<0$. This uses $e^{9/5}>1+9/5+(9/5)^2/2>100/23$. There is no positive real pole. Indeed, $D'_v(s)$ starts negative, decreases until $D_v''(s)$ changes sign, and then increases to infinity. Its positive zero $s_c$ satisfies $s_c<2\sqrt v$, since $D'_v(2\sqrt v)>0$ by the defining inequality for $v<v_*$. At the minimum $D_v(s_c)=2v-s_c^2/2>0$.

For an upper-half-plane pole $z=(u-1)+i\theta$, the imaginary equation is $(1-v)e^{u-1}\sin\theta=u\theta$. If $\sin\theta\le0$, then $\theta\ge\pi$, $u\le0$ and $|u|\le e^{-1}/\theta$. The real part $(u^2+1-\theta^2)/2-2v$ of the quadratic is then less than $-1$, while the exponential has modulus at most $e^{-1}$. Thus $u>0$ and $\theta\in(2\pi k,(2k+1)\pi)$ for some $k\ge0$.

Put $b=\theta\cot\theta$ and $d=\theta^2\csc^2\theta$. The real and imaginary equations together give

$$
u=b\pm\sqrt{d-1+4v},\qquad
G_v(\theta):=u-1-\log u-\log(\theta/\sin\theta)+\log(1-v)=0.
\tag{2}
$$

On each positive $u$ branch, differentiating $u^2-2bu+1-\theta^2-4v=0$ gives

$$
\theta(u-b)G'_v(\theta)=-u(b-1)^2-\theta^2(u-1)^2/u<0.
\tag{3}
$$

The right side can vanish only if $u=b=1$, which would contradict the quadratic. The plus branch is positive throughout $(0,\pi)$, and $G_v(0)>0$. At $\theta=1$, the alternating Taylor bounds give $u\ge2\cot1>1$, $\cot1\le13/20$, $\csc^2 1-1\le11/25$ and $\sin1\le101/120$. On $v\in[j/10,(j+1)/10]$, $j=0,1,2,3$, these give $u<U_j$, with $U_j=8/5,9/5,2,21/10$. Using $\log x\ge2(x-1)/(x+1)$ for $x\ge1$ and $\log(1-v)\le-v$,

$$
G_v(1)\le\frac{(U_j-1)^2}{U_j+1}-\frac{38}{221}-\frac j{10}<0.
$$

Therefore (3) gives exactly one plus-branch root with $0<\theta<1$. It has $u>1$, since the branch starts at $1+2\sqrt v$ and at any first crossing of $u=1$ its $G_v$ value is already negative. A positive minus branch in $(0,\pi)$ occurs only when $v<1/4$ and $0<\theta<\sqrt{1-4v}$. There $G_v$ increases by (3). Its initial value $-2\sqrt v-\log(1-2\sqrt v)+\log(1-v)$ is positive, since the derivative in $\sqrt v$ is positive on $(0,1/2)$. This excludes any pole on that branch. On each higher interval $k\ge1$, the product $1-\theta^2-4v$ of the quadratic roots in $u$ is negative. Hence only the plus branch is positive, and there is at most one pole by (3).

Write $z=s+i\theta$ for the unique principal upper pole, with $s>0$ and $0<\theta<1$. All complex poles are simple because at a zero of $D_v$,

$$
D'_v(z)=z^2/2-2v,
\tag{4}
$$

which can vanish only on the real axis. Conjugation supplies the lower poles. The other upper poles have imaginary parts greater than $2\pi k$, at most one for each $k\ge1$.

## Moduli and the negative real pole

Factor $D_v(w)=(w-z)(w-\bar z)(w+R)g(w)$. The quadratic subtracted from $(1-v)e^w$ in (1) is its interpolating polynomial at $z,\bar z,-R$. The exponential interpolation remainder, in simplex integral form, gives

$$
g(w)=(1-v)\int_{\alpha+\beta+\gamma+\delta=1\atop \alpha,\beta,\gamma,\delta\ge0}
\exp(\alpha z+\beta\bar z-\gamma R+\delta w)\,d\sigma ,
\tag{5}
$$

where $d\sigma$ is simplex coordinate measure of total mass $1/6$. This is the Hermite–Genocchi formula for the third divided difference of the exponential, including repeated arguments by continuity. [de Boor, equations (50) and (52)](https://pages.cs.wisc.edu/~deboor/sat/papers/2/2.pdf#page=19)

For real $w$, averaging under interchanging $\alpha,\beta$ replaces the phase by the positive factor $\cos((\alpha-\beta)\theta)$. Hence $c_1=(\log g)'(0)$ and $c_2=(\log g)''(0)$ are the mean and variance of $\delta\in[0,1]$ under a positive probability measure. In particular $c_1\ge0$ and $c_2\le c_1(1-c_1)$. Also $D_v(0)=v$ and $D'_v(0)=D''_v(0)=-v$. The logarithmic derivatives of the factorization give, with $r_0=|z|$ and $h=1+c_1$,

$$
\frac{2s}{r_0^2}=\frac1R+h,
\qquad
\frac{2}{r_0^2}=\frac1{R^2}+\left(\frac1R+h\right)^2-2-c_2 .
$$

Using the variance bound in the second identity gives

$$
\frac{R^2}{r_0^2}
=1+hR+\frac{h^2-2-c_2}{2}R^2
\ge 1+R-R^2/2
\ge 1+R/10 .
\tag{6}
$$

Thus $r_0<R$. Write $r=r_0/R$. As $R<9/5$ and $\log(1+R/10)\ge R/(10+R)>R/12$, we have $r\le e^{-R/24}$. Comparing (5) at $w=z$ and $w=-R$ gives

$$
\frac{|g(z)|}{g(-R)}
\le\frac{e^{s+R}}{\cos\theta}\le e^{3R}.
\tag{7}
$$

Indeed, the complex integral at $z$ costs at most $e^{s+R}$ relative to the underlying positive integral at $-R$, where the cosine is at least $\cos\theta$. Here $s<R$, $\theta<R$ and $-\log\cos\theta\le\theta^2<R$ by $\theta<1$, $\cos\theta\ge1-\theta^2/2$ and $-\log(1-x)\le x/(1-x)$.

We also have $\varphi:=\arg z<\pi/3$. For $v\to0$, the negative root $R$ tends to zero since $D_0(-r)<0$ for $r>0$ by the exponential Taylor remainder. By (6), $z\to0$, and (1) gives $z^3/v\to-6$, so the first-quadrant root has $\varphi\to\pi/3$. For all $v$ in the interval write $D_v(z)=v(2-e^z)+z^3 I(z)$ with $I(z)=\frac12\int_0^1(1-t)^2 e^{tz}\,dt$. The phase of $I(z)$ lies in $(0,\theta)$, and $2-e^z$ has negative imaginary part. Since $D_v(z)=0$, the continuous quantity $3\varphi+\arg I(z)-\arg(2-e^z)$ is an odd multiple of $\pi$. It tends to $\pi$ as $v\to0$, so equals $\pi$ throughout. Both additional terms are positive, giving $0<\varphi<\pi/3$.

## Uniform residue margins and sign alternation

Put $N=n+1$ and normalize the principal conjugate residues by

$$
M_n(q)=\frac{2}{(1+q)|D'_v(z)|\,r_0^N},\qquad
\Phi_n(q)=N\varphi+\arg D'_v(z),\qquad
B=\frac{\sin\varphi}{|1+z/R|}.
$$

Here $\arg D'_v(z)\in(0,\pi)$ by (4) and $s>0$. The residue sum for $O_n(-q)/n!$ follows by integrating $1/((1+q)w^N D_v(w))$ over squares with real and imaginary coordinates $\pm 2\pi M$. On horizontal sides the imaginary part of $D_v(w)$ is $-(1+\Re w)\Im w$. Where $|1+\Re w|\ge1$ this bounds its modulus below by $2\pi M$. On the rest its real part grows quadratically in $M$. On vertical sides the exponential dominates on the right and the quadratic term dominates on the left. The integrals tend to zero, and the other complex residues are absolutely summable by (4) and their imaginary-part bounds. The contribution of every pole to the coefficient is minus its residue, since the residue at the origin equals the coefficient.

The normalized coefficient has the form $-\cos\Phi_n$ plus the normalized negative real residue and an error $E_N$ from the other complex poles. The negative real residue has absolute value

$$
\frac{|D'_v(z)|}{2D'_v(-R)}r^N
=B\frac{|g(z)|}{g(-R)}r^{N+1}\le B e^{-R}
\qquad(n\ge94).
\tag{8}
$$

The identity follows by differentiating the three-root factorization at $z,-R$. The bound uses $N+1\ge96$, (6), and (7). For (5) at $z$, $|g(z)|\le e^R/6<4/3$, and therefore $|D'_v(z)|\le(16/3)\theta R$. At every other upper pole $z_k$ of index $k\ge1$, (4) gives $|D'_v(z_k)|\ge17k^2$, since $|z_k|>2\pi k$, $v<1/3$ and $\pi>3$. Grouping complex conjugate residues and using $r_0<R<9/5$ then gives

$$
|E_N|\le \theta R(3/10)^N.
\tag{9}
$$

Here the coefficient factor $(16/51)\sum_{k\ge1}k^{-N-2}$ is less than one. Since $B\ge\theta/(2R)$, the total absolute normalized error in the cosine formula is bounded by

$$
B e^{-R}+|E_N|\le B(1-R/4)<1
\qquad(n\ge94).
\tag{10}
$$

Indeed, $1-e^{-R}\ge R/(1+R)>5R/14$ and $|E_N|/B\le(18/5)R(3/10)^N<R/16$. Also $B<1$.

As $q\downarrow q_*$, the principal $\theta$ tends to zero because $G_{v_*}(0)=0$ and (3) excludes any positive limiting angle. Formula (2) then gives $s=2\sqrt v+O(\theta^2)$, so $\arg D'_v(z)\to\pi/2$. At $q\to\infty$ we have $z\sim(6v)^{1/3}e^{i\pi/3}$ and $D'_v(z)\sim z^2/2$. Thus the phase runs continuously from $\pi/2$ to $(n+3)\pi/3$. For $m=\lfloor n/3\rfloor$, prepare ordered disjoint brackets with phase inside $(j\pi,(j+1)\pi)$, $j=1,\ldots,m$, using the last hit of the lower level before the first hit of the upper one. These levels occur in the endpoint range except for the last upper level when $n=3m$. If that level has no finite hit, use the last hit of $m\pi$ followed by the ray to infinity. Its leading sign at infinity is $(-1)^m$, opposite to the sign at $m\pi$. In all other brackets (10) gives opposite signs at the finite endpoints. Thus there is exactly one simple negative root in each bracket by the degree, and $\sin\Phi_n$ has sign $(-1)^j$ at the $j$th root in increasing modulus.

At such a root, (10) gives $|\cos\Phi_n|\le B(1-R/4)$. Add $1/R$ times the exponential coefficient $O_n(-q)/n!$ to $O_{n+1}(-q)/(n+1)!$. The negative real pole cancels exactly. After dividing by $M_{n+1}$, the principal complex terms become

$$
\sin\Phi_n\sin\varphi-(\cos\varphi+r)\cos\Phi_n,
$$

with error at most $2\theta R(3/10)^N$. Let $A=\sin\varphi$ and $C=\cos\varphi+r>1/2$, so that $B=A/\sqrt{A^2+C^2}$. The sine term has magnitude exceeding the cosine term by at least

$$
A\sqrt{1-B^2}-CB(1-R/4)=CBR/4\ge\theta/16.
$$

The remaining error is strictly smaller. Since the old coefficient vanishes at the tested point, the sign of $O_{n+1}(-q)$ is $(-1)^j$. From the positive value at $q=0$, these signs force one root before the first old root and one between each consecutive pair. If the degree increases, the leading sign at infinity forces one further root after the last old root. This proves strict consecutive interlacing for pairs beginning at $n\ge94$.

## Finite verification

The [checker](code/threshold_three_check.py) reconstructs the finite prefix by the first-block recurrence and by the delayed recurrence

$$
O_{n+1}=(n+1)O_n+2t O_n'+(n+\tbinom n2)O_{n-1}
 +\tbinom n2 t\bigl(O_{n-2}+(t-1)O'_{n-2}\bigr).
$$

The latter follows by extracting coefficients of $(1-z-z^2/2)H_z=(2+(t-1)z^2/2)tH_t+(1+z+t z^2/2)H$, where $H$ is the row generating function. Positive coefficients and exact Sturm counts give simple negative roots for all 95 rows. For each consecutive pair the signed Euclidean remainder degrees drop one at a time with positive leading coefficients and end at a nonzero constant. This verifies the orientation by evaluating the recursion at each root from the preceding step. At equal degrees one first replaces the old row by its remainder on division by the new row. The remainder has the same values at the new roots, so the sign condition puts one old root before the leftmost new root and one in each gap. The check also verifies the displayed rational comparisons. An independent check through $n=96$ used associated Stirling numbers for the large blocks and then added all ordered singleton and doubleton completions.

~~~sh
python -I -O topics/ordered-large-blocks/code/threshold_three_check.py
~~~

## Scope

This proves the ordered threshold $j=3$. The other all-row threshold in this work is [$j=2$](threshold-two.md). The author’s status page and public investigation #108 were checked on 25 November 2026. Targeted web and Firecrawl searches for consecutive interlacing and real-rootedness of the ordered threshold-three polynomials did not locate a previous proof. The unordered triple threshold and the restricted singleton-or-large family have different definitions and prior results. [Author’s status page](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Public investigation #108](https://github.com/1337isnot1337/solved-conjectures/issues/108) · [Related restricted cases](https://www.symmetricfunctions.com/realRootedSetPartitions.htm#bigBlockSetPartitions)
