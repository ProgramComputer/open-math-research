# Extreme zeros of fixed powers of the Eulerian matrix

Let $A(n,k)$ count permutations of $[n]$ with $k-1$ descents for $1\le k\le n$, and take $A(0,0)=1$. Fix an integer $p\ge1$ and form the ordinary matrix power $A^p$. The following calculation extends the high-degree estimate in the [two-ended theorem for the square](endpoint-asymptotics.md). It concerns the largest-modulus zeros of a row. Mao and Wang ask for all the zeros of the square. [Original conjecture](https://arxiv.org/abs/2607.01572)

## The cluster at each exponential scale

For $h\ge1$ set $v=(h+1)/h$ and $\alpha_j=h^{-(p-j)}v^{-(h-1)(j-1)}$, $1\le j\le p$. Define
$$
F_{p,h}(u)=\sum_{r=0}^{p}v^{-\binom r2} e_r(\alpha_1,\ldots,\alpha_p)u^r.
$$
Its zeros $-x_1,\dots,-x_p$ are distinct and negative. Order their moduli increasingly. They satisfy $x_{j+1}>v x_j$. For each fixed $h$ and all sufficiently large $n$, the $p$ zeros of row $n$ with modulus ranks $p(h-1)+j$, in order from largest, are simple and negative, and
$$
 \beta_{n,p(h-1)+j} \sim -v^n/x_j \qquad(1\le j\le p).
$$
Writing $a$ for any fixed positive modulus rank gives $\beta_{n+1,a}<\beta_{n,a}<\beta_{n+1,a+1}$ eventually. For $p=2$ this recovers the two roots on each successive scale. The case $p=1$ specializes to the previously known extreme-zero asymptotic for ordinary Eulerian polynomials. [Durán, Theorem 2](https://arxiv.org/abs/2404.03249)

## Proof

Let $q_{n,i}=(A^p)(n,n-i)$ for $0\le i<n$. Write $e_{m,b}$ for the Eulerian number with exactly $b$ descents. Eulerian symmetry and ordinary matrix multiplication give
$$
q_{n,i}=\sum_{b_1+\cdots+b_p=i}
  \prod_{j=1}^p e_{n-b_1-\cdots-b_{j-1},b_j},
$$
where all indices in the sum are nonnegative. The Eulerian coefficient bound and its fixed-index asymptotic give $e_{m,b}\le(b+1)^m$ and $e_{m,b}/(b+1)^m\to1$ as $m\to\infty$. Both follow from the explicit Eulerian formula. [Derivation](endpoint-asymptotics.md)

Put $M_i=\max_{\sum b_j=i}\prod_j(b_j+1)$. A transfer of one unit from a larger part to a part smaller by at least two strictly increases the product. Hence at $i=p(h-1)+r$, $0\le r\le p$, the maximum is $M_i=h^{p-r}(h+1)^r$. It is attained exactly at $b_j=h-1+\epsilon_j$ with $\epsilon_j\in\{0,1\}$ and $\sum_j\epsilon_j=r$.

For fixed $i$, only the maximizing compositions contribute in the limit of $q_{n,i}/M_i^n$. The contribution of one maximizing composition is
$$
\prod_j (h+\epsilon_j)^{-((j-1)(h-1)+\sum_{\ell<j}\epsilon_\ell)}.
$$
Writing $h+\epsilon_j=h v^{\epsilon_j}$ shows that this product equals
$$
 h^{-(h-1)\binom p2}\ v^{-\binom r2}
 \prod_{j:\epsilon_j=1} h^{-(p-j)}v^{-(h-1)(j-1)}.
$$
Here each chosen index $j$ contributes to $p-j$ later prefix sums, and each pair of chosen indices contributes once to $\binom r2$. Summing gives the coefficients of $F_{p,h}$ times a positive common factor.

Let $s=1/v$. Successive ratios of $M_i$ are equal to $v$ across this block and strictly decrease between blocks. Consequently $M_i s^i$ takes its maximum $D$ precisely at $i=p(h-1),\ldots,ph$. The uniform bound
$$
 q_{n,i}\le \binom{i+p-1}{p-1}M_i^n
$$
follows by retaining all compositions and discarding their nonpositive exponent corrections. Since $M_i\le(1+i/p)^p$, it grows at most polynomially. Thus after scaling $z=s^n u$ and dividing by $D^n$, the reverse polynomial $\sum_{i=0}^{n-1}q_{n,i}z^i$ converges locally uniformly to $h^{-(h-1)\binom p2}u^{p(h-1)}F_{p,h}(u)$. Indeed for all sufficiently large $i$, $M_i s^i/D\le e^{-\eta i}$ for some $\eta>0$, and the resulting geometric bound dominates the tail on each fixed disk.

For arbitrary positive $\alpha_1,\ldots,\alpha_p$ and $v>1$, inserting another $\alpha$ into the elementary symmetric functions changes the polynomial $F(u)$ into $F(u)+\alpha uF(u/v)$. Suppose $G(x)=F(-x)$ has positive zero moduli $x_1<\cdots<x_m$ with $v x_i<x_{i+1}$ and $G(0)=1$. At $x_i$ and at $vx_i$ the polynomial $G(x)-\alpha x G(x/v)$ has sign $(-1)^i$. It is positive at zero and its leading coefficient has sign $(-1)^{m+1}$. Hence it has one root in each of $(0,x_1),(vx_1,x_2),\ldots,(vx_{m-1},x_m),(vx_m,\infty)$. These account for the degree and are simple. The displayed intervals give a ratio greater than $v$ between consecutive new roots. Starting with $1+\alpha_1u$ proves the claimed spacing.

Rouché's theorem on small disjoint disks around the simple negative limit roots gives exactly one zero in each disk. It is real by complex conjugation. Circles centered at zero between the limiting moduli give their precise positions among all complex zeros, counting multiplicity. Inverting the zeros gives the stated asymptotics. Within one cluster the inequality $x_{j+1}>v x_j$ gives the strict interlacing at the same scale. Across clusters the next exponential base is strictly smaller. This proves the consecutive-row claim for every fixed modulus rank.

## Scope and checks

The project screened the Eulerian clause as an unresolved claim. Searches of the original paper, its public research issue and arXiv for ordinary powers of the shifted Eulerian matrix and extreme-root asymptotics located the known $p=1$ case. The paper treats powers of several other triangular matrices. This comparison does not establish priority for every possible formulation. [Mao–Wang](https://arxiv.org/abs/2607.01572) · [Public Eulerian investigation](https://github.com/1337isnot1337/solved-conjectures/issues/83) · [Prior-work check for the square](endpoint-asymptotics.md#prior-work-checked)
