# Why the two consecutive rows need the same cycle weight

Write $Q_{N,k}(t,u)=\sum_\pi u^{c(\pi)-1}t^{\operatorname{exc}(\pi)-1}$, over permutations of $N$ letters with all cycles of size at least $k$. Here $0^0=1$. The [cycle-weight deformation](cycle-marking.md) uses the same $u$ in both rows. One possible route to a proof is to allow two independently chosen weights in $[0,1]$ and establish that every new row interlaces every old row. This stronger assertion fails for arbitrarily small positive differences of the weights.

**Theorem.** Fix $0\le u<v\le1$. For every sufficiently large integer $m$, choose any real $m<\rho<m+1$ and any sequence with $N\to\infty$, $N/k\to\rho$. For all sufficiently large $N$ the $m$th nonzero-root modulus of the new row at weight $v$ is strictly *larger* than the $m$th modulus of the old row at weight $u$. Both roots are negative and simple. If the two rows strictly interlaced with all roots real, the new row would have the smaller modulus at this rank. For $(u,v)=(0,1)$ the obstruction holds for every $m\ge2$.

## Coefficients at a fixed rank

Let $b_{N,p}(u)=[t^{p-1}]Q_{N,k}(t,u)/p^N$. Encode each permutation by its maximal decreasing runs around its cycles, assign the $p$ run colors, and divide by the $p!$ equivalent run labelings. Then $b_{N,p}(u)$ is the weighted probability of acceptance for a uniform word of length $N$ on $p$ colors and an independent uniform permutation of those colors. On acceptance, its weight is $u^{c-1}$ with $c$ the number of cycles of the color permutation. In particular $0\le b_{N,p}(u)\le1$. The event that every color occurs in both halves of the label set guarantees the upward run boundaries and has probability tending to one for fixed $p$. In a cycle containing $j$ colors the fraction of the $N$ labels tends in probability to $j/p$, by the binomial variance bound. [Run encoding](proof.md) · [Exterior-root argument](effective-front.md)

For $p=m$, every color cycle exceeds the threshold with probability tending to one since $1/m>1/\rho$. For $p=m+1$ the surviving color permutations are exactly the fixed-point-free ones up to an error tending to zero. Indeed $1/(m+1)<1/\rho<2/(m+1)$ for $m\ge2$. These limits hold in both rows since $(N+1)/k\to\rho$ as well. Define
$$
M_m(u)=\frac{1}{m!}\sum_{\sigma\in S_m}u^{c(\sigma)-1},
\qquad D_{m+1}(u)=\frac{1}{(m+1)!}
   \sum_{\substack{\sigma\in S_{m+1}\\\mathrm{fix}(\sigma)=0}}u^{c(\sigma)-1},
\qquad H_m(u)=M_m(u)/D_{m+1}(u).
$$
Thus the two normalized coefficients tend respectively to $M_m(u)$ and $D_{m+1}(u)$. Both are positive even at $u=0$ because a full cycle is always admitted.

Set $a_N=(m/(m+1))^N b_{N,m}(u)/b_{N,m+1}(u)$. After substituting $t=a_N z$ and dividing $Q_{N,k}$ by its positive coefficient of $z^{m-1}$, the two middle terms are $z^{m-1}(1+z)$. The other terms tend to zero uniformly on every compact annulus. To see this, strip off the bounded factor $b_{N,m}/b_{N,m+1}$ from the radius and compare $p^N(m/(m+1))^{Np}$ at consecutive indices. On the right, starting after $p=m+1$, each outward ratio is at most $(1-1/(m+1)^2)^N$. On the left it is at most $(1-1/m^2)^N$. The $b_{N,p}$ are bounded by one and the two central coefficients remain bounded below. The tails are therefore dominated by geometric series, even though the total degree grows.

Rouché's theorem on $|z|=1/2$, $|z|=2$ and on a small circle about $-1$ gives exactly $m-1$ roots inside the smaller circle, $m$ inside the larger one, and one simple negative root tending to $-1$ in the scaled variable. The latter is real by complex conjugation. This locates rank $m$ in modulus even without assuming real-rootedness of the full weighted rows. The ratio of its new modulus to its old modulus tends to
$$
\frac{m}{m+1}\frac{H_m(v)}{H_m(u)}. \tag{1}
$$

## The dependence on the cycle weight

For $u>0$, insertion of one new label in a permutation gives $M_m(u)=\prod_{j=1}^{m-1}(u+j)/m!$. In the probability distribution proportional to $u^{c(\sigma)}$ on $S_p$, the sum of the probabilities that each prescribed $j$-set consists of fixed points, counted over all such sets, is
$$
\binom pj u^j\frac{u(u+1)\cdots(u+p-j-1)}{u(u+1)\cdots(u+p-1)}
\longrightarrow u^j/j!\qquad (p\to\infty)
$$
for each fixed $j$, with an empty product equal to one. The even and odd Bonferroni bounds therefore show that the probability of no fixed points tends to $e^{-u}$. Also $M_m(u)/M_{m+1}(u)=(m+1)/(m+u)$. At $u=0$ one has $H_m(0)=(m+1)/m$ by counting full cycles. Consequently $H_m(u)\to e^u$ throughout the stated range of fixed weights. The right side of (1) tends to $e^{v-u}>1$ as $m\to\infty$, proving the theorem.

At the particular endpoints $u=0,v=1$, (1) reduces to $(m/(m+1))^2/D_{m+1}(1)$. The alternating sum for derangements gives $D_{m+1}(1)\le3/8$ for $m\ge2$ (the odd partial sums lie below the even ones, and the even sums decrease from $p=4$). Since $(2/3)^2>3/8$, this ratio exceeds one for every such $m$. For example when $2<N/k<3$ with limiting ratio in the open interval, the new-to-old second-root ratio tends to $4/3$. With identical weights, (1) instead gives $m/(m+1)$.

## A finite rational witness

Take old size $48$, minimum cycle length $21$, and old and new cycle weights $0$ and $1$. There are at most two cycles in the new size. With $A_j$ the ordinary Eulerian polynomial, the two polynomials are
$$
p=A_{47},\qquad q=A_{48}+t\sum_{j=21}^{28}\binom{48}{j-1} A_{j-1}A_{48-j}.
$$
Distinguish the cycle containing the first label. At the rational number $x=-2^{-26}$, the exact integer calculation gives
$$
-2^{62}<q'(x)p(x)-q(x)p'(x)<-2^{61},\qquad p(x)>0 .
$$
For monic strictly interlacing $p,q$ with $\deg q=\deg p+1$, the residues of $q/p$ at the zeros of $p$ are strictly negative. Its derivative is therefore positive everywhere it is defined on the real line. The negative Wronskian excludes that interlacing. The checker reconstructs the Eulerian polynomials by insertion and by the independent finite-difference coefficient formula. It also compares the two-cycle expansion with direct insertion at the positive weight. [Exact checker](verify_independent_cycle_weights.py)

The fixed-weight original conjecture remains open. This argument identifies a specific loss incurred by independent control of the two rows. **⬜ None.** No Lean or Rocq proof is recorded.
