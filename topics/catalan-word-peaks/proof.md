# Real-rootedness and consecutive interlacing for strict peaks in Catalan words

Let $C_n(t)$ count Catalan words by strict peaks. The argument below gives $\lfloor(n-1)/2\rfloor$ simple negative zeros for every $n\ge150$, and the exact prefix verifies the remaining rows. Together they establish all-row real-rootedness. The proof of strict consecutive interlacing uses these bounds and the two effective endpoint comparisons.

The four branch points, the radial cut expansion, and the phase-index method are from the public eventual theorem. The new estimates bound all the required phase-node errors explicitly and supply an effective overlap with the checked prefix. [Prior eventual theorem, §§1, 2 and 5](https://github.com/1337isnot1337/solved-conjectures/blob/research/research/alexandersson-catalan-peaks/EVENTUAL-ZEROS.md) · [Alexandersson's conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjCatalanWordPeaks)

## Exact rays and the checkpoint range

Write $d=\cos\theta$ for $0<\theta<\pi/2$ and put
$$
a=(1+2d)^{-1/2},\qquad
c=\frac{2d^2(1+d)}{(1+2d)^{3/2}},\qquad t=1-c^{-2}.
$$
Increasing $\theta$ decreases $c$ and $t$. The generating function for short peaks, specialized to strict peaks, gives
$$
\sum_{n\ge0}c^n C_n(t)x^n
=\frac{1-x^2-\sqrt{D_c(x)}}{2x(c-x)},
\qquad D_c(x)=(1+x^2)^2-4cx .
$$
[Baril–Harris–Harry–McClinton–Ramírez, Theorem 5.1](https://arxiv.org/html/2404.05672v1#S5.Thmtheorem1)

The four roots are $z,\bar z,w,\bar w$, where $z=ae^{i\theta}$ and $w=a^{-1}e^{i\theta'}$, with $\cos\theta'=-a^2d$ and $\pi/2<\theta'<\pi-\theta$. To check this, substitute $z$ into $z^3+2z+1/z=4c$. The quartic has no real roots because $c<4/(3\sqrt3)$, the minimum of $(1+x^2)^2/(4x)$ on $x>0$. The sum and product of its roots identify the other conjugate pair. The strict angle bound follows from $\cos\theta'>-d$.

For each branch point $\zeta$ let
$$
B_\zeta(x)=-\frac{\prod_{\nu\ne\zeta}\sqrt{1-x/\nu}}{2x(c-x)}
$$
where the square roots are principal. Cauchy deformation to the four radial cuts gives the coefficient as the sum over the four roots of
$$
-\frac{\zeta^{-n}}{\pi}B_\zeta(\zeta)b(n) \mathbb E_n[H_\zeta(S)],\qquad
b(n)=\int_0^\infty s^{1/2}(1+s)^{-n-1}\,ds,
$$
where $S$ has probability density $s^{1/2}(1+s)^{-n-1}/b(n)$ and
$$
H_\zeta(s)=\frac{B_\zeta(\zeta(1+s))}{B_\zeta(\zeta)}
=\frac{1}{(1+s)(1+b_0s)}
 \prod_{\nu\ne\zeta}\sqrt{1+b_\nu s},
\qquad b_0=\frac{\zeta}{\zeta-c},\quad b_\nu=\frac{\zeta}{\zeta-\nu}.
\tag{1}
$$
This is the jump of the factor $\sqrt{1-x/\zeta}$, whose top-minus-bottom boundary value along $x=\zeta(1+s)$ is $-2i\sqrt{s}$. Continuing the branch along the positive real axis makes the apparent pole at $x=c$ removable, since the square root there equals $1-c^2$. The small arcs at the branch points vanish, and the function is bounded on sufficiently large circles by its rationalized formula, so the outer coefficient integral vanishes for $n\ge1$. Each square-root ratio in (1) is continued from its value one and is the principal square root along the indicated line.

Let $\gamma=\arg(-B_z(z))$ be the continuous phase and $\Psi_n=n\theta-\gamma$. At a branch point, $c-z=(1-z^2)^2/(4z)$. The factors from the other conjugate pair have product
$$
(1-z/w)(1-z/\bar w)=1+2a^4d e^{i\theta}+a^4e^{2i\theta},
$$
whose argument is $\arctan(\sin\theta/(1+2d))$, by calculating its positive real and imaginary parts. The other factor is $1-e^{2i\theta}=2\sin\theta\,e^{i(\theta-\pi/2)}$. Also $1-z^2$ has positive real part. Thus
$$
\gamma=\frac{\theta}{2}-\frac{\pi}{4}
       +\frac12\arctan\frac{\sin\theta}{1+2d}
       +2\arctan\frac{d\sin\theta}{1+d-d^2}.
\tag{2}
$$
In particular
$$
-\frac{\pi}{4}\le\gamma\le \frac{\pi}{8}+1,\qquad
\gamma(0)=-\frac{\pi}{4},\quad
\gamma(\pi/2)=\frac{\pi}{8}.
$$
The upper bound uses $d\sin\theta\le1/2$ and $1+d-d^2\ge1$.

Write $n=2m+\delta$ with $\delta\in\{1,2\}$ and put $\Delta=\pi/2-\theta$. At every checkpoint $\Psi_n=k\pi$ with $1\le k\le m-1$,
$$
n\theta\ge3\pi/4,\qquad
n\Delta\ge(1+\delta/2)\pi-\pi/8-1 .
\tag{3}
$$
In particular the second lower bound is $11\pi/8-1$ in odd rows and $15\pi/8-1$ in even rows.

## Bounds on the radial integrals

For the ray at $z$ the three coefficients $b_\nu$ in (1) have moduli bounded respectively by
$$
(2\sin\theta)^{-1},\quad (2d)^{-1},\quad 1.
$$
The first is the conjugate coefficient. The second follows from $|w/z|=a^{-2}=1+2d$, and the third from $\cos(\theta+\theta')<0$. When $\theta\le\pi/4$, the second is less than one. When $\theta\ge\pi/4$, the first is less than one. The remaining coefficient has modulus $\ell\le n/4$ in either case. Indeed, $\sin x\ge(89/100)x$ on $0\le x\le\pi/4$ by Taylor's inequality, and $\pi>31/10$ in (3) gives $n\sin\theta>2$ in the first range and $nd>29/10$ in the second.

Let $K_z(s)$ denote the three square-root factors multiplied together, with one coefficient of modulus $\ell$ and the other two of modulus at most one. For a principal root $g=\sqrt{1+us}$ we have $|g|\le1+|u|s/2$ and $|g-1|=|u|s/|g+1|\le|u|s$. The product of the two bounded factors has modulus at most $1+s$, using the stronger bound $|g|\le\sqrt{1+s}$ for each. Their product differs from one by at most $2s+s^2/2$. It follows that
$$
|K_z(s)|\le(1+s)(1+\ell s/2),\qquad
|K_z(s)-1|\le(\ell+2)s+(\ell+1/2)s^2 .
\tag{4}
$$

Let $R_z(s)=1/((1+s)(1+b_0s))$ be the remaining factor. We have
$$
|b_0|=\frac{4a^2}{|1-z^2|^2}
     =\frac{1+2d}{1+2d-2d^3}\le3 .
$$
Consequently for $s\le1/8$, $|R_z|\le8/5$ and $|R_z-1|\le(29/5)s$. For the latter use the telescoping difference of $(1+s)^{-1}$ and $(1+b_0s)^{-1}$ from one. Since $H_z=R_z K_z$, (4) bounds the expectation of $|H_z-1|$ restricted to this range by
$$
\left(\frac{2n}{5}+9\right)\frac{3/2}{n-3/2}
+\left(\frac{2n}{5}+\frac45\right)
  \frac{15/4}{(n-3/2)(n-5/2)}
<\frac{71}{100}\quad(n\ge150).
\tag{5}
$$
Here the two fractions are the first and second beta moments of $S$, and the bound at $n=150$ decreases thereafter.

For every $s\ge0$ we have $|R_z(s)|\le 2n/(1+s)$ at these checkpoints. If $\theta\le\pi/4$, then $c>2/5$ by the formula for $c$ and $d\ge1/\sqrt2>7/10$. Thus
$$
\frac{|c-z|}{|c-(1+s)z|}
\le\frac{c+a}{c\sin\theta}
\le\frac{7}{2\sin\theta}<2n .
$$
If $\theta\ge\pi/4$, use instead the imaginary part of $(1+s)z$ to bound the first ratio by $(c+a)/(a\sin\theta)\le7\sqrt2/3<4$ because $c/a\le4/3$. By (4), the full tail loss is bounded pointwise by $2n(1+ns/8)+1$. Put $N=\lceil n/4\rceil$. Since $(1+s)^{-(n-N)}\le(8/9)^{n-N}$ on this tail, and $b(N)/b(n)\le16$, its expectation is at most
$$
16(8/9)^{n-N}\left(2n\left(1+\frac n8\frac{3/2}{N-3/2}\right)+1\right)
<60n(8/9)^{n-\lceil n/4\rceil}<\frac1{50}.
\tag{6}
$$
For the beta ratio bound use $b(n)=\pi c_{n-1}/(2n)$ with $c_j=\binom{2j}{j}/4^j$, and $1/(2\sqrt j)\le c_j\le1/\sqrt{j+1}$ by induction. The last inequality in (6) is checked at $n=150,151,152,153$ by rational arithmetic and then improves stepwise in each residue class.

For the ray at $w$ the coefficients from $\bar w,\bar z$ have modulus at most one, and the coefficient from $z$ has modulus at most $(1-a^2)^{-1}=1+(2d)^{-1}\le 1+n/4$. The first bound uses $\sin\theta'\ge \sqrt{8/9}$. The second uses $\cos(\theta+\theta')<0$, and the third is the reverse triangle inequality. Also $\Re(w/(w-c))>0$, so $|R_w(s)|\le1/(1+s)$. Therefore
$$
\mathbb E_n |H_w(S)|\le1+(1+n/4)\frac{3}{4(n-3/2)}<6/5
\qquad(n\ge150).
$$
The ratio of amplitudes at the endpoints of the rays simplifies to
$$
\frac{|B_w(w)|}{|B_z(z)|}
=\sqrt{\frac{\sin\theta'}{\sin\theta}}\frac{|c-z|}{|c-w|}
\le \frac1{\sqrt{\sin\theta}} .
\tag{7}
$$
For this identity the two cross-pair distances cancel, each contributing a factor $a^{-1}$ in the numerator that cancels with $a^2$ from the denominators. Also $|c-w|>|c-z|$ since $\Re w<0<\Re z$ and $|w|>|z|$.

The $w$ pair after normalization by the leading $z$-pair amplitude is bounded by $(6/5)a^{2n}/\sqrt{\sin\theta}$. If $\theta\le\pi/4$, this is less than $(6/5)n2^{-n}$. If $\theta\ge\pi/4$, the prefactor is less than $36/25$. For $d\ge1/4$ the factor $a^{2n}$ is at most $(2/3)^n$. For $d<1/4$, (3) gives $nd>29/10$ and hence
$$
a^{2n}=\exp(-n\log(1+2d))<e^{-58/15}<1/40
$$
using $\log(1+2d)\ge 2d/(1+2d)>4d/3$. In all cases the remote contribution has modulus less than $1/25$ in these units.

Combining (5), (6), and (7), the absolute error relative to the leading $z$-pair amplitude is less than $71/100+1/50+1/25<1$. Since the leading cosine equals $(-1)^k$ at a checkpoint, the full value $C_n(t)$ has the same sign.

## Exact root count

When $n\ge150$, choose the checkpoints for $k=1,\dots,m-1$ in strictly increasing order of $\theta$. Continuity suffices: the phase starts at $\pi/4$, ends at $n\pi/2-\pi/8>(m-1)\pi$, and after any hit of one level a later hit of the next level follows by the intermediate value theorem. The alternating signs give at least $m-2$ distinct roots in the intervals between these selected checkpoints.

Since $C_n(0)>0$ and the first checkpoint has negative sign, a further root lies between $t=0$ and that checkpoint. At the last checkpoint the sign is $(-1)^{m-1}$, while sufficiently far down the negative axis it is $(-1)^m$ by the positive leading coefficient. This gives another root in a disjoint interval. The resulting $m$ roots exhaust the degree and are all simple. For $0\le n\le150$, an exact prefix calculation gives the full simple-negative root count.

For the consecutive comparison, note that $\Psi_n$ is strictly increasing. In (2) the absolute derivatives of $\sin\theta/(1+2d)$ and $d\sin\theta/(1+d-d^2)$ are bounded by $3$ and $3/2$, respectively. Thus $|\gamma'|\le5<n$. In particular the old root of rank $j=k+1$ in increasing absolute value is between the $k$th and $(k+1)$st phase levels, for $1\le k\le m-2$. Bounds (3) therefore hold at every such middle root. For fixed $\theta$, all radial estimates obtained from those bounds continue to hold if $n$ is increased by one.

## Comparing the two exact ray averages

Write $J_n=\mathbb E_n[H_z(S)]$. Positively rescale the original polynomial as
$$
Y_n=\operatorname{Re}(e^{-i\Psi_n}J_n)+r_n ,
$$
where $r_n$ is the contribution of the $w$ pair. This uses the normalization $2a^{-n}|B_z(z)|b(n)/\pi$ for $c^n C_n(t)$. In the middle range just identified, (5)–(7) give $|J_n-1|<73/100$ and $|r_n|,|r_{n+1}|<1/25$. For $\theta\le\pi/4$ the sharper remote estimate in the proof of (7) gives $|r_n|,|r_{n+1}|<1/(100n)$.

The size-$n+1$ probability measure is obtained from the size-$n$ measure by tilting by $u(S)=(1+S)^{-1}$. Thus
$$
J_{n+1}-J_n=\frac{\operatorname{Cov}_n(H_z,u)}{\mathbb E_n u},\qquad
\mathbb E_n u=\frac{n-1/2}{n+1}.
\tag{8}
$$
The covariance here is $\mathbb E_n[(H_z-\mathbb E_n H_z)(u-\mathbb E_n u)]$. Put $M_j=\mathbb E_n S^j$ and $e=3/(2n)$. Then $|u-\mathbb E_n u|\le S+e$, and also $|u-\mathbb E_n u|\le1$. The beta moments are
$$
M_j=\frac{(3/2)_j}{(n-3/2)(n-5/2)\cdots(n-j-1/2)},\qquad
\operatorname{Var}_n(S)=\frac{(3/2)n}{(n-3/2)^2(n-5/2)}.
$$

For all estimates below, the tail $S>1/6$ has expected contribution less than $1/(20n)$ as long as its integrand is bounded by $(2n+1)(1+nS/8)$. Indeed the same tilt to $N=\lceil n/4\rceil$ used in (6) bounds this expectation by $60n(6/7)^{n-N}$. Multiplying by $n$ gives a function less than $1/20$ at each of $n=150,151,152,153$. It decreases thereafter in each residue class, since $((n+4)/n)^2(6/7)^3<1$.

First consider $\theta\le\pi/4$. Let $g(s)=\sqrt{1+b_{\bar z}s}$ be the factor from the conjugate of the principal branch point. Then $\Re b_{\bar z}=1/2$, so $\Re g\ge1$ and $|g'|\le\ell/2$. On $s\le1/6$, $|R_z|\le2$ and $|R_z-1|\le7s$. Combining this with the bounds on the two short factors gives
$$
|H_z(s)-g(s)|\le (1+\ell s/2)(11s+s^2)
\le 11s+(1+11n/8)s^2+(n/8)s^3.
\tag{9}
$$
The tail of $|H_z-g|$ satisfies the preceding pointwise hypothesis by the global bounds on $H_z$ and $g$. Consequently
$$
1-\Re J_n\le11M_1+(1+11n/8)M_2+(n/8)M_3+1/(20n)<3/20 .
\tag{10}
$$

For the covariance of $g$ with $u$, use independent copies $S,S'$ and the product difference identity
$$
2\operatorname{Cov}_n(g,u)=\mathbb E_n[(g(S)-g(S'))(u(S)-u(S'))].
$$
The two Lipschitz bounds $\ell/2$ and $1$ give $|\operatorname{Cov}_n(g,u)|\le(\ell/2)\operatorname{Var}_n(S)$. For the covariance of $H_z-g$ use (9) multiplied by $S+e$ on the local interval, and the same tail bound because $|u-\mathbb E_n u|\le1$. Thus with $F_j=M_{j+1}+eM_j$,
$$
|J_{n+1}-J_n|
\le
\frac{(n/8)\operatorname{Var}_n(S)+11F_1+(1+11n/8)F_2+(n/8)F_3+1/(20n)}
     {(n-1/2)/(n+1)}
<\frac1n.
\tag{11}
$$

For $\theta\ge\pi/4$, use all three factors in (4). On the same local interval,
$$
|H_z(s)-1|\le2|K_z(s)-1|+7s
\le (n/2+11)s+(n/2+1)s^2.
$$
Again the tail satisfies the global pointwise hypothesis. As a constant has zero covariance, (8) gives
$$
|J_{n+1}-J_n|
\le\frac{(n/2+11)F_1+(n/2+1)F_2+1/(20n)}
          {(n-1/2)/(n+1)}
<\frac4n.
\tag{12}
$$

The numerical inequalities (10)–(12) are rational checks at $n=150$. For (11) and (12) first multiply both sides by $n$. The resulting upper bounds decrease with $n$ because $n^jM_j$ decreases, all coefficients are sums of nonnegative multiples of nonpositive powers of $n$ after inserting the scaled moments, and $(n-1/2)/(n+1)$ increases. Likewise $n^2\operatorname{Var}_n(S)$ decreases. This proves the asserted bounds at all larger sizes.

## Strict signs at the old roots

Let $t<0$ be an old middle root of rank $j=k+1$. Put $Z=e^{-i\Psi_n}J_n$. Then $\Re Z=-r_n$. Since $|J_n-1|<73/100<\sin(\pi/3)$, its argument has absolute value less than $\pi/3$. At the old root the corrected phase $\Psi_n-\arg J_n$ has cosine of absolute value less than $(1/25)/(27/100)<1/2$. The old phase itself is between $k\pi$ and $(k+1)\pi$. If the corrected phase fell outside that interval it could differ from an endpoint by at most $\pi/3$, contradicting the cosine bound. Hence $\Im Z$ has sign $(-1)^{k+1}$.

At the same value of $t$, the next phase is $\Psi_n+\theta$, so
$$
Y_{n+1}=\sin\theta\,\Im Z-\cos\theta\,r_n+r_{n+1}
       +\operatorname{Re}\bigl(e^{-i(\Psi_n+\theta)}(J_{n+1}-J_n)\bigr).
$$
For $\theta\le\pi/4$, (10) and the remote bound give $|\Im Z|>4/5$, and $\sin\theta>2/n$. The leading term dominates $1/n+2/(100n)$ from (11) and the two distant values. For $\theta\ge\pi/4$, $|\Im Z|>\sqrt{(27/100)^2-(1/25)^2}>1/4$ and $\sin\theta>7/10$. The leading term dominates $4/n+2/25$ from (12) and the distant values. Thus in both ranges $Y_{n+1}$, hence $C_{n+1}(t)$, has sign $(-1)^j$.

For the old rightmost root, the effective vertical-slit comparison already gives $C_{n+1}(t)<0$, the sign for rank one. For the old farthest root the effective reversed-polynomial comparison gives the sign $(-1)^m$. When the old row is odd, its farthest root lies to the left of all roots of the next even row of degree $m$. When the old row is even, its farthest root is between the two farthest roots of the next odd row of degree $m+1$. [Right-edge proof](effective-right-edge.md) · [Far-left proof](far-left.md)

We now have sign $(-1)^j$ at every old root of rank $j$. Starting at $t=0$, where $C_{n+1}(0)>0$, this forces one new root before the first old root in increasing modulus and one between each consecutive old pair. If the degree increases, the leading sign also forces a new root beyond the last old root. These roots exhaust the degree and give strict consecutive interlacing in the indicated orientation for $n\ge150$. The exact prefix then supplies the remaining pairs.


## Exact finite interface

The independent finite replay reconstructs each row in two ways. One uses
$$
[u^k]C_n(1+u)=\frac1{n-k}\binom{n-k}{k}\binom{2n-3k}{n-2k-1},
$$
and the other uses the coefficient recurrence of
$$
F=1+(1-t)x^2F+x(1+(t-1)x)F^2 .
$$
The two coefficient lists agree with the retained archive for $0\le n\le150$. For each row the signed rational Sturm chain ends in a constant and counts full degree on $(-\infty,0)$. For each consecutive pair of positive degree, start the signed remainder chain with the new row and the old row when the degree increases, or with the new row and the old row reduced modulo the new one for equal degrees. Every step drops the degree by one, with positive leading coefficient, and the chain ends in a nonzero constant. This gives simple alternating roots by the signed remainder identities. In the equal-degree case the remainder has the old row's sign at every new root, positive at the rightmost new root, which fixes the orientation. Constant rows are included vacuously.

The replay also checks the rational constants in (5), (6), and (10)–(12). From the research repository root, with Python and python-flint installed, run
~~~
python -I -O topics/catalan-word-peaks/code/verify_all_rows.py topics/catalan-word-peaks/results/family-rows.jsonl
~~~
This reproduces 151 full simple-negative root counts and 150 strict oriented pairs.
