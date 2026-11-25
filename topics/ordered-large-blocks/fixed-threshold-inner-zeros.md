# Consecutive interlacing on an interval at every fixed threshold

Fix a block threshold $j\ge2$. Write $D(z,q)=1-S(z)+qC(z)$ with $S(z)=\sum_{a=1}^{j-1}z^a/a!$ and $C(z)=\sum_{a\ge j}z^a/a!$. Let $q_*$ and $\rho>0$ be the critical parameter and its double zero from the [sharp lower-edge theorem](lower-spectral-edge.md). That theorem gives $O_{n,j}(-q)>0$ throughout $0\le q\le q_*$ for every $n$, and $\rho$ is the only zero of $D(\cdot,q_*)$ on or inside $|z|=\rho$.

**Theorem.** For every fixed $j$ there is a nonempty interval immediately to the right of $q_*$ on which all sufficiently large consecutive rows have strictly alternating simple real zeros in the variable $q$. The number of such zeros in each row grows linearly with $n$. More precisely there is an analytic phase $\phi(q)>0$ on that interval with $\phi(q_*)=0$ by continuity, and for each sufficiently small fixed $q_0>q_*$,
$$
 \#\{q\in(0,q_0]:O_{n,j}(-q)=0\}=\frac{n\phi(q_0)}{\pi}+O(1).
$$
At each fixed index $h\ge1$ the $h$th positive real zero satisfies
$$
 n^2(q_{n,h}-q_*)\longrightarrow
  \frac{\rho^2D_{zz}(\rho,q_*)}{2C(\rho)}\pi^2 h^2 .
$$
This theorem controls the real zeros at the inner edge. The companion [outer-edge theorem](fixed-threshold-outer-zeros.md) controls largest moduli among all complex zeros.

**The two poles near the double zero.** At the fold, $D_q=C(\rho)>0$ and $D_{zz}(\rho,q_*)>0$ by the double-zero minimum. Solve $D(z,q)=0$ as $q=Q(z)$. Then
$$
 Q(z)=q_*-\frac{D_{zz}(\rho,q_*)}{2C(\rho)}(z-\rho)^2+O((z-\rho)^3).
$$
Taking an analytic square root of the nonvanishing factor in $(q_*-Q(z))/(z-\rho)^2$ and inverting locally gives, at $q=q_*+t^2$, a branch $z(t)=\rho+i\sqrt{2C(\rho)/D_{zz}(\rho,q_*)}\,t+O(t^2)$. The other zero is $z(-t)$, the conjugate for real $t$. Write
$$
 \phi(t)=\frac{\log z(t)-\log z(-t)}{2i},\qquad
 r(t)=\exp\big((\log z(t)+\log z(-t))/2\big),
$$
choosing the real logarithm at $\rho$. The first function is odd and has positive derivative $\kappa=\sqrt{2C(\rho)/D_{zz}(\rho,q_*)}/\rho$. Use $\phi$ itself as the analytic parameter. Then $q(\phi)=q_*+\phi^2/\kappa^2+O(\phi^4)$ is even and strictly increasing for small positive $\phi$. The two poles are $r(\phi)e^{\pm i\phi}$.

**Uniform coefficient estimate.** Isolation at the fold gives a circle $|z|=R>\rho$ containing just the double zero at $q=q_*$. For small complex $\phi$ there are just the two continuations inside and $D$ stays uniformly away from zero on that circle. Put $N=n+1$ and $f_n(q)=O_{n,j}(-q)/n!$. Cauchy's formula enlarged to this circle gives the negative of the two residues of $1/(z^N D)$, with an analytic remainder $J_n$ satisfying $|J_n|\le C_0 R^{-n}$. This remainder is even in $\phi$ by its contour representation.

Write $D_z(r(\phi)e^{i\phi},q(\phi))=i\phi d(\phi)$, where $d(0)=\rho D_{zz}(\rho,q_*)>0$. Define the even and odd analytic functions $a$ and $B$ by
$$
 a(\phi)=\exp\big((\log d(\phi)+\log d(-\phi))/2\big),\qquad
 B(\phi)=(\log d(\phi)-\log d(-\phi))/(2i).
$$
On the real axis $a>0$ and $B$ is real. Substitution of the residues gives the signed identity
$$
 \frac{\phi a(\phi)r(\phi)^N}{2} f_n(q(\phi))
 =\sin(N\phi+B(\phi))+E_n(\phi),\qquad
 E_n=\phi a(\phi)r(\phi)^N J_n/2 .
$$
It extends analytically across zero. On a fixed smaller complex disk, $|E_n(\phi)|\le C_1|\phi|\sigma^n$ and $|E_n'(\phi)|\le C_2\sigma^n$ for some $\sigma<1$. Indeed $|r|<R$ on the larger disk after shrinking, and the derivative estimate follows by Cauchy's inequality.

**Counting and consecutive order.** On a fixed small interval $0\le\phi\le2\eta$, the phase $N\phi+B(\phi)$ starts at zero and has derivative $N+O(1)$. Wherever its distance from $\pi\mathbb Z$ is at least $\pi/6$, the sine has modulus at least $1/2$. In each full band within $\pi/6$ of $h\pi$, the right-hand side is strictly monotone since the principal derivative has modulus at least $\sqrt3(N-O(1))/2$ and fixed sign. Its endpoint signs are opposite. The half-band at the origin has just its forced zero from the normalizing factor. Thus the roots in $0<\phi<\eta$ have consecutive indices starting at one, one per complete band, with at most one unfinished band at the counting endpoint. The phase-count formula follows, and each root is simple in $q$ by $q'(\phi)>0$.

At the old $h$th zero, write $U=N\phi+B(\phi)$. Then $|\sin U|\le C_1\phi\sigma^n$ and $\cos U$ has sign $(-1)^h$ and magnitude at least $\sqrt3/2$. In the next row the phase is $U+\phi$. Because $\sin\phi\ge\phi/2$ for small positive $\phi$, the term $\cos U\sin\phi$ controls the sign even at the first band. The other two terms have combined magnitude $O(\phi\sigma^n)$. Thus the next row has sign $(-1)^h$ at the old zero. Taking $\eta<\pi/12$ ensures that the new phase at any old zero in $0<\phi<\eta$ is within $\pi/3$ of the same center $h\pi$. Its sign and the uniqueness and orientation of the new crossing put the new $h$th zero before the old $h$th zero, which is before the new $(h+1)$st zero. The larger interval $0\le\phi\le2\eta$ provides the final comparison for large $n$. This proves strict consecutive alternation, including an initial number of zeros proportional to $n$.

Finally fixed $h$ gives $(n+1)\phi\to h\pi$ by the residue estimate, bounded index, and $B(0)=0$. Substituting into $q(\phi)$ gives the constant. $\square$

## The microscopic limit and derivatives

The preceding two-pole calculation gives a locally uniform limit in a complex neighborhood after rescaling. In fact, uniformly on every compact subset of the entire $x$-plane,
$$
 \frac{O_{n,j}(-q_*-x/n^2)}{O_{n,j}(-q_*)}
 \longrightarrow S_\kappa(x)
 =\frac{\sin(\kappa\sqrt{x})}{\kappa\sqrt{x}}
 ={}_0F_1\!\left(;\tfrac32;-\frac{\kappa^2x}{4}\right),
$$
with the value at zero defined by continuity. To see this first write $x=y^2$. For bounded complex $y$, $\phi=\kappa y/n+O(n^{-3})$, $r(\phi)^{n+1}/\rho^{n+1}\to1$ and $a(\phi)\to a(0)$. The normalized error divided by $\phi$ is exponentially small. The sine divided by $\phi(n+1)$ converges uniformly to $\sin(\kappa y)/(\kappa y)$, including zero, by taking the analytic extension of $\sin u/u$. In particular the value of $f_n$ at the fold is asymptotic to $2(n+1)\rho^{-(n+1)}/a(0)$. Dividing by this exact positive value proves the stated convergence; both sides are even in $y$.

For every fixed integer $h\ge0$, all nonzero $h$th row derivatives are positive at every point of $[-q_*,0]$. Indeed their exponential generating function at $-q$ is $h!C(z)^h/D(z,q)^{h+1}$. The critical positivity and its subcritical extension imply strictly positive coefficients whenever $n\ge jh$. For $q>q_*$ this generating function is analytic on the positive real axis, tends to zero at positive infinity, and is nonpolynomial. The Pringsheim argument of the sharp-edge theorem therefore gives infinitely many rows with negative $h$th derivative at $-q$.

Locally uniform convergence gives convergence of every fixed derivative of the rescaled polynomial. Since
$$
 S_\kappa^{(h)}(x)=
 \frac{(-\kappa^2/4)^h}{(3/2)_h}\,
 {}_0F_1\!\left(;h+\tfrac32;-\frac{\kappa^2 x}{4}\right),
$$
its positive zeros are $b_{h+1/2,k}^2/\kappa^2$, where $b_{\nu,k}$ is the $k$th positive zero of the Bessel function $J_\nu$. These zeros are simple. For each fixed $k$, apply uniform convergence on small disks about the first $k$ zeros and on their intervening real compact intervals. Rouché's theorem, conjugation, and the absence of earlier real zeros below the fold identify the first $k$ negative real roots of the row derivative. If $q_{n,h,k}$ is the $k$th smallest positive modulus among these real roots, then
$$
 \lim_{n\to\infty} n^2(q_{n,h,k}-q_*)=\frac{b_{h+1/2,k}^2}{\kappa^2}.
$$
For $h=0$ this recovers $b_{1/2,k}=k\pi$. [Bessel series](https://dlmf.nist.gov/10.2.E2) · [Positive zeros of $J_\nu$](https://dlmf.nist.gov/10.21.i)
