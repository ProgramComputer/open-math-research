# Consecutive excedance interlacing at every threshold from size 100,000

Let $E_{n,k}(t)$ enumerate permutations on $n$ labels by excedances when all cycles have length at least $k$, and put $P_n=E_{n,k}/t$ at fixed $k$.

**Theorem.** For $n\ge100000$ and every $3\le k\le n$, all $n-2$ zeros of $P_n$ are simple and negative. They strictly interlace the zeros of $P_{n+1}$ with the next row supplying both outer zeros. Zero itself is a simple common root of the unreduced rows. Alexandersson's conjecture concerns every size. Formal verification of this result is ⬜ None. [Original statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances)

The proof controls the value and the angular derivative together. Its rational certificate comprises eleven intervals in the continuous parameter $x=n/k$. It uses the [signed-pole product](../uniform-hilbert/README.md), the [exterior-root theorem](../effective-front.md), the [differentiated common-residue comparison](../differentiated-residues/README.md) at large $x$, and the [lower-size common contour](../lower-circle/README.md). The two latter inputs are specified in the final join below.

## Cycle probabilities

Write $D(u)=\exp(\sum_{j\ge k}u^j/j)=\sum_r d_r u^r$. Here $d_0=1$, $d_j=0$ for $0<j<k$, and $r d_r=\sum_{j=0}^{r-k}d_j$ for $r\ge k$. Therefore $d_r=1/r$ on $[k,2k)$ and $1/(2k-1)\le d_r\le1/k$ for $r\ge k$. For $k\ge100$ we also have

$$
 k d_r\le4/7\quad(r\ge2k),\qquad
 k d_r\ge547/1000\quad(r\ge3k).
$$

For $2k\le r<3k$, put $y=r/k-1$. The decreasing integral bound gives $r d_r\le1+1/k+\log y$. The tangent of $\log$ at $7/4$, together with $1/k+\log(7/4)<4/7$, makes this at most $(4/7)(1+y)$. For $r\ge3k$ use induction after summing $d_k$ through $d_{2k-1}$, whose sum is at most $\log 2+1/k$. The upper estimate follows from $1+\log 2+(1+4/7)/k<12/7$. For $3k\le r<4k$, the same harmonic sum is at least $\log 2$. In the following block we may use $kd_j\ge1/2$, hence $k d_r\ge1/2+(\log 2-1/2)/(r/k)>547/1000$. For $r\ge4k$, the contribution of $d_0$ and the blocks $[k,2k)$ and $[2k,3k)$ is at least $1+\log 2+1/2>4(547/1000)$. Induction proves the lower bound.

Let $b_s$ be the coefficient of $u^s$ in $(1-u)(D(u)-1)$. There is an atom $b_k=1/k$. For $k<s<2k$, $|b_s|=1/(s(s-1))$. The jump at $2k$ is positive and below $1/(4k^2)$. For $j\ge2$, the coefficients at $jk<s\le(j+1)k$ satisfy $|b_s|\le1/(2j!k^2)$. Indeed $s b_s=d_{s-k}-d_{s-1}$ on the second block and both probabilities are between $1/(2k-1)$ and $1/k$. On the following blocks $s b_s=-\sum_{i=s-k+1}^{s-1}b_i$ divides the preceding block maximum by at least $j$, also when part of the sum is in the current block. [Cycle differences](../cycle-probability-variation.md)

## A two-dimensional sign test

For $0<\theta\le\pi/2$ put $t=-\exp(-\pi\cot\theta)$, $S=\sin\theta$, $C=\cos\theta$, and $z_a=(C+iaS)^{-1}$ with $\rho_a=|z_a|$ for odd integers $a$. Use $F_j=(\pi/S)^j E_{j,k}(t)/(j!(1-t)^j)$, $B_j=\sum_a z_a^j$, and $m=n+1-k$. A prime on $F_j$ or $z_a$ denotes an angular derivative. At an old zero the exact insertion normalization gives $(n+1)F_{n+1}=SF'_n+B_kF_m$.

Consider the two real vectors

$$
 V_{\pm}=k\left(F_n,\frac{F'_n}{n}\pm\frac{B_k F_m}{nS}\right),
 \qquad U_n=2kd_n(\cos(n\theta),-\sin(n\theta)).
$$

It suffices to show $`\Vert V_{\pm}-U_n\Vert_2<2kd_n`$ for both signs. The strict disk inequality gives $`V_{\pm}\cdot U_n>0`$. At $`\theta=j\pi/n`$ this gives the sign of $`F_n`$. At an old zero the second coordinates have the sign of $`-\sin(n\theta)`$. This also gives simplicity there, since the average of the two second coordinates is $`kF'_n/n`$. At an old root between the integer phases $`j\pi`$ and $`(j+1)\pi`$, the sign of $`P_{n+1}`$ is $`(-1)^j`$ after division by $`t<0`$.

Use the partial-fraction identity

$$
 F_M=\sum_a [u^M](D(z_a u)-1)Q_a(u),\qquad
 Q_a(u)=\prod_{q\ne a}\left(1+\sum_{s\ge k}
   \frac{b_s z_q^{s-1}u^s}{i(q-a)S}\right),\quad M\in\lbrace n,m\rbrace .
$$

It follows by distinguishing one pole in each nonempty occupied set in $\prod_q D(z_q u)$. The constant term of $Q_a$ gives the single-pole contribution $d_M B_M$. All pole sums contributing a fixed coefficient and its derivative converge locally absolutely in the indicated angular range. [Partial fractions and the insertion formula](../uniform-hilbert/README.md)

For the remaining factors let $T$ denote total non-distinguished degree and $r=M-T\ge k$. Write $h$ for a term of the coefficient of $u^T$ in $Q_a-1$. Conjugate symmetry permits summing the real part of each term over all signed indices. In the old row, $y=r/n$ and the contribution from $z_a^r h$ to the joint vector, before the derivative of $h$, has norm at most

$$
 \rho_a^r |h|\left(\max(1,y|a|)+y(a^2-1)S\rho_a^2\right).
$$

Indeed the matrix on the real and imaginary parts of $z_a^r h$ has top row $(1,0)$ and bottom row $(y\Re(z'_a/z_a),-y\Im(z'_a/z_a))$. The real and imaginary parts of $z'_a/z_a$ are $-(a^2-1)SC\rho_a^2$ and $-a\rho_a^2$. Bound the diagonal matrix and its one off-diagonal entry separately. The latter entry is zero for $|a|=1$. For the others

$$
 y(a^2-1)S\rho_a^r\le |a|\rho_a^{r/2}/\sqrt n.
$$

In fact $(1+v)^{r/4}\ge1+rv/4\ge\sqrt{rv}$ at $v=(a^2-1)S^2$ and $r\ge4$. The derivative of $h$ contributes at most $\rho_a^r |h'|/n$ to the norm. Retaining the real two-coordinate matrix here avoids charging the principal poles twice for the same coefficient.

## Bounds by degree

Fix an interval $\ell\le x=n/k\le X$ in the certificate and let $k\ge K$, $kS\ge A$, $nS^2\ge u_0=6/5$. Here $K\ge1000$. For degree $s$ use bin $i=\lceil Bs/k\rceil$ with $B=4$. Attach a factor $v^i$ to each primitive term before taking products. A product uses the sum $b$ of its bin indices. Different products contributing to one coefficient of degree $T$ can therefore occupy different bins. For a nonempty product of total degree $T$, every primitive degree is at least $k$, so

$$
 \max(1,b/(B+1))\le T/k\le b/B.
$$

In particular a contributing product has $b\le(B+1)X$. All coefficientwise upper bounds below are sums of absolute contributions. Expansion and differentiation can therefore be performed with nonnegative binned polynomials, keeping just these bin indices.

For each bin use an upper bound $v_i$ on $k\sum_s|b_s|$ and a lower bound $g_i$ on $s/k$. Include the singleton $i=B$ with $g_i=v_i=1$. On $(g,g+1/B]$ inside the first block $1<s/k\le2$, use

$$
 v_i=\frac{1}{g-1/K}-\frac{1}{g+1/B}
     +\frac{\mathbf 1_{i=2B}}{4K},\qquad g_i=g .
$$

This follows by telescoping $1/(s(s-1))$ at the two integer endpoints and allowing separately for the jump. In block $j\ge2$ use $g_i=(i-1)/B$ and $v_i=(1/B+1/K)/(2j!)$ since a bin contains at most $k/B+1$ integers. No primitive degree above $Xk$ can contribute.

Put $W_p(c)=(1+c(p^2-1))^{-96}$. Bernoulli's inequality gives $\rho_q^{s-1}\le W_q(c_i)$ with $c_i=(g_i-1/K)u_0/(192X)$ because $s-1\ge192$ and $(s-1)S^2\ge(g_i-1/K)u_0/X$. Define

$$
 U(c)=\sup_a\sum_{q\ne a}\frac{W_q(c)}{|q-a|},\qquad
 U_1(c)=\sup_a\sum_{q\ne a}\frac{|q|W_q(c)}{|q-a|}.
$$

The linear factors summed over all $q\ne a$ have coefficient majorant $L(v)$ in the bin variable. Their angular derivatives divided by $n$ have majorant $J(v)$, where

$$
 L_i=v_i U(c_i)/A,\qquad
 J_i=v_i\left(\frac{(i/B)U_1(c_i)}{\ell A}
                  +\frac{U(c_i)}{K u_0}\right).
$$

The derivative uses $|z'_q/z_q|\le|q|$ and $|(1/S)'|\le1/S^2$. For a fixed bin $i$ these estimates hold after summing over the primitive degrees in the bin, uniformly in $a$. Expanding the product of distinct factors and then allowing repetitions gives the majorant $Q=\exp L-1$ for $Q_a-1$. Differentiating one marked factor gives $J\exp L$ for $Q'_a/n$. This retains degree information even after taking the supremum over the distinguished pole.

For bin $b$ write $h=b/B$, $g=\max(1,b/(B+1))$. Omit $g+1>X$ since then $r<k$. For the old row use

$$
 y_- =\max(1/X,1-h/\ell),\qquad y_+=1-g/X.
$$

They bound $r/n$ from below and above. For the residual row $M=m$ use the lower bound $y_m=\max(1/X,1-(h+1)/\ell)$. Set $w=4/7$ when $\ell-h\ge2$ and $w=1$ otherwise, and set $w_m=4/7$ when $\ell-1-h\ge2$ and $w_m=1$ otherwise. These bound $k d_r$ in the corresponding rows. With $c=y_-u_0/192$ and $W(c)=\sum_a W_a(c)$, the three costs from this bin are bounded by

$$
\begin{aligned}
 V_b &=
 w Q_b\left(\sum_a W_a(c)\max(1,y_+|a|)
 +\frac{\sum_{|a|>1}|a|W_a(c/2)}{\sqrt{K\ell}}\right),\\
 D_b &= w [v^b](J\exp L) W(c),\\
 Z_b &= w_m Q_b W(y_m u_0/192).
\end{aligned}
$$

The first two bounds control the joint norm. The last controls $k|F_m-d_mB_m|$. The previously proved single-pole tails in $B_n$ and $B_n'/n$ are below $1/50$ and $1/16$ respectively after excluding the principal pair. Their joint error multiplied by $k d_n$ is less than $0.038$. As $m\ge3k$ here, the normalized insertion lag is bounded by

$$
 I=\frac{W(u_0/(192X))}{A\ell}
       \left((4/7)W((1-1/\ell)u_0/192)+\sum_b Z_b\right).
$$

Thus each disk inequality holds if $1.094-0.038-I-\sum_b(V_b+D_b)>0$.

## Exact intervals and joins

The [checker](verify_degree_blocks.py) encloses both signed pole lattices by keeping $|p|\le63$ and rounding upward on the grid $2^{-56}$. Writing $P=63$, the omitted first moment is at most $(1+c(P^2-1))^{-95}/(190c)$ by integrating the decreasing weighted kernel beyond $P$ on each odd lattice. The omitted mass is at most this divided by $P$. In computing the two suprema $U,U_1$, the omitted kernel is at most half the corresponding tail because distinct odd indices differ by at least two. For the retained lattice it is enough to check distinguished indices through $P+2$ in absolute value, since every retained denominator increases farther out. The exponential majorant uses the recurrence $b[v^b]\exp L=\sum_{i=1}^b i L_i[v^{b-i}]\exp L$, with outward rounding in every bin.

| Lower bound on $n$ | Interval for $x=n/k$ | Sufficient $A$ |
| ---: | --- | ---: |
| 100,000 | $[4,6], [6,10], [10,16], [16,25]$ | $10$ |
| 100,000 | $[25,34]$ | $9$ |
| 100,000 | $[34,42]$ | $8$ |
| 100,000 | $[42,50]$ | $27/4$ |
| 100,000 | $[50,62], [62,75]$ | $7$ |
| 100,000 | $[75,86]$ | $27/4$ |
| 120,000 | $[86,96]$ | $7$ |

For each interval $K=\lfloor n_{\min}/X\rfloor$. The least certified disk margin exceeds $65716/10^6$. [Exact output](verified-output.txt)

For $x<4$ the [three-cycle theorem](../three-cycle-complete.md) gives the result. In the intervals up to $x=50$ the middle condition $nS^2\ge6/5$ already implies $kS\ge\sqrt{(6/5)n}/X\ge A$. For the remaining displayed intervals $kS\ge3$ at every middle point. If $kS<A$ then $kS^2<A^2/K\le1/25$. The differentiated common-residue comparison applies at $x\ge50$, $kS\ge3$, $kS^2\le1/25$ and $nS^2\ge6/5$. Both comparisons give the same old signs at integer phase samples and the same actual next-row signs at old roots, even when the estimate used changes inside a gap. The [exterior-root theorem](../effective-front.md) supplies the first $\lfloor7\sqrt n/20\rfloor$ root ranks at each end, with the last exterior root preceding the first middle sample. Reciprocity and degree give exactly one old root in each remaining gap, including the central root for odd $n$. The signs at all old roots and the endpoint coefficients then give strict consecutive interlacing.

For $100000\le n<120000$ use the table through $x=86$. At $x\ge86$, $0.89x>47+2.5\log n$ because $\log 120000<11.7$. For $120000\le n<4062720$ use the full table, then the same inequality at $x\ge96$ since $\log 4062720<15.3$. The lower-size radial theorem applies under this inequality for $k\ge400$, $n\ge10000$, and the small-threshold circle covers $4\le k<400$ from $55000$. The [threshold-three theorem](../fixed-threshold.md) covers $k=3$ at every size. For $n\ge4062720$ use the [earlier uniform result](../adaptive-poles/README.md).

This is an analytic proof with finite rational certificates for its constants. Below $100000$ the general conjecture is open in the range left by the other sufficient conditions.

[Independent agent-assisted review](review.md) · [Independent rational checker](verify-independent.py) · [Independent results](independent-output.txt)


**Reproduction.** From this directory, run the following two standard-library programs.

~~~sh
python3 -I -B verify_degree_blocks.py
python3 -I -B verify-independent.py
~~~

**Source check, November 26, 2026.** Alexandersson lists consecutive interlacing for the excedance statistic on permutations with every cycle of length at least the given cutoff. Native GitHub issue searches for `"excedance" "minimum cycle length" "interlacing"` and code searches for `"long-cycle excedances" "angular derivative"` returned no results. Indexed web and X searches by author, minimum cycle length, excedances, interlacing and joint degree estimates surfaced no competing proof of this cutoff. Newly published or unindexed work can escape those searches. [Original statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Related prior-art search](../differentiated-residues/literature.md)
