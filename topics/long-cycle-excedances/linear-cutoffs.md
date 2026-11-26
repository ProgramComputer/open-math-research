# All the zeros for a growing minimum cycle length

**Supporting theorem.** For all sufficiently large $n$ and every integer $k$ with
$$
 3\le k\le n,\qquad k\ge\frac{100n}{\log n},
$$
the excedance polynomial $E_{n,k}$ for permutations all of whose cycles have length at least $k$ has a simple zero at zero and $n-2$ distinct negative zeros. The cutoff in $n$ is uniform over $k$ and the logarithms are natural. In particular, this includes the range $k\ge\alpha n$ for every fixed $\alpha>0$. The [uniform interlacing proof](uniform-interlacing.md) uses the mixed-pole estimates below to establish the consecutive comparisons. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsPermutations) · [Single-row combinatorial bounds](proof.md) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)

Write $a_h=[t^h]E_{n,k}(t)$. All the allowed permutations are derangements, and inversion interchanges $h$ and $n-h$ excedances. The unique decreasing cyclic run gives $a_1=a_{n-1}=1$ and the degree is $n-1$. We will prove that $E_{n,k}$ has sign $(-1)^j$ at
$$
 t_j=-\exp(-\pi\cot(j\pi/n)),\qquad 1\le j<n.
$$
Reciprocity gives the signs above $j=n/2$ from those below it, since $t_{n-j}=1/t_j$ and $E_{n,k}(t)=t^n E_{n,k}(1/t)$. Signs at consecutive samples give $n-2$ different open intervals and use up the entire nonzero degree.

## Samples closest to zero

Set $J=\lfloor\tfrac14\sqrt{n/\log n}\rfloor$. The decreasing-run encoding in the linked argument gives $a_h\le h^n$ in all ranks and $a_h\ge h^{n-1}/2$ for $h\le J+1$ and large $n$, uniformly in $k$. Indeed a single cycle on the $h$ run colors has probability $1/h$, and the probability of a missing color or a failed upward boundary is at most $2h\exp(-\lfloor n/2\rfloor/h)$. These estimates include $h=1$ directly.

For $1\le j\le J$ write $s=\pi\cot(j\pi/n)=n/j+O(j/n)$, by the Taylor expansion at zero. Consider the majorant $b_h=h^n e^{-s h}$. It is log-concave, and
$$
 b_{j+1}/b_j\le \exp(-n/(2j(j+1))+O(j/n)),\qquad
 b_{j-1}/b_j\le \exp(-n/(2j^2)+O(j/n))\quad(j>1).
$$
Use $x-\log(1+x)\ge x^2/(2(1+x))$ and $\log(1-x)+x\le-x^2/2$. Both ratios are at most $n^{-3}$ for sufficiently large $n$. The two geometric tails together are at most $2b_j n^{-3}/(1-n^{-3})$. The $j$th term has size at least $b_j/(2j)$, hence fixes the sign at $t_j$.

## A partial fraction expansion for cycles

Let $t=-e^{-s}$, $s\ge0$, and set $\theta=\mathrm{arccot}(s/\pi)\in(0,\pi/2]$. An $a$-cycle has excedance polynomial $t A_{a-1}(t)$, where $A_{a-1}$ is the ordinary Eulerian polynomial. For $a\ge2$,
$$
 \frac{t A_{a-1}(t)}{(a-1)!(1-t)^a}=\sum_{p\in2\mathbb Z+1}(s+i p\pi)^{-a}.
$$
For $s>0$ this is the result of differentiating $-1/(e^s+1)=\sum_{h\ge1}(-1)^h e^{-sh}$ exactly $a-1$ times with $-d/ds$, and using the partial fractions of the hyperbolic tangent. More explicitly, the symmetric partial fraction sum of $(s+i p\pi)^{-1}$ is $\tfrac12\tanh(s/2)=\tfrac12-1/(e^s+1)$, by the logarithmic derivative of the product of $\cosh(s/2)$ over its zeros. The differentiated series converges locally uniformly, including at $s=0$. The Eulerian power-sum formula gives the displayed identity on the series side.

Write $z_p=(\cos\theta+i p\sin\theta)^{-1}$, so $z_{\pm1}=e^{\mp i\theta}$, and put $\rho=(s^2+\pi^2)^{-1/2}$. The exponential formula for a labelled set of cycles now expresses $E_{n,k}(t)/(n!(1-t)^n\rho^n)$ as
$$
 \sum_{\ell=1}^{\lfloor L\rfloor}\frac1{\ell!}
 \sum_{\substack{a_1+\cdots+a_\ell=n\\a_i\ge k}}
 \frac1{a_1\cdots a_\ell}
 \prod_{i=1}^{\ell}\sum_{p\ {\rm odd}} z_p^{a_i},
 \qquad L=n/k .
$$
The exponential formula is also the starting point of Alexandersson’s computational analysis of this family. [Author’s derivation and recurrence](https://github.com/PerAlexandersson/RealRooted/issues/2590#issuecomment-7059794955)

When every cycle takes the same $p$, its combined contribution is $d_n\sum_p z_p^n$, where $d_n$ is the probability a uniform permutation of $n$ satisfies the cycle restriction. In particular $d_n\ge1/n$ from single cycles.

## Cancellation between different poles

We work uniformly on $J\pi/n\le\theta\le\pi/2$ and write $S=\sin\theta$. For all sufficiently large $n$, $J\ge\tfrac15\sqrt{n/\log n}$, so
$$
 S\ge\sin(J\pi/n)\ge 2J/n\ge\frac{2}{5\sqrt{n\log n}}.
$$
Define $P=\sum_{p\ {\rm odd}} |z_p|^{k-1}$. The two indices $p=\pm1$ each contribute one. For every other odd $p$, $p^2-1\ge p^2/2$ and Bernoulli's inequality gives
$$
 |z_p|^{k-1}=(1+(p^2-1)S^2)^{-(k-1)/2}
 \le \frac{1}{1+(k-1)p^2 S^2/4}.
$$
Extending the sum on each side to all positive integer magnitudes and integrating the decreasing kernel gives
$$
 P\le 2+2\int_0^\infty\frac{dx}{1+(k-1)x^2 S^2/4}
   =2+\frac{2\pi}{S\sqrt{k-1}}
   \le25\sqrt{L\log n}.
$$
In the last step use $k-1\ge k/2$, $k=n/L$, and $5\sqrt2\pi<23$.

Fix a tuple of pole indices with at least two distinct entries. Assign it to the lexicographically first pair of slots with distinct indices, written $p,r$. This choice depends only on the indices. Fix every length outside this pair. If the two selected lengths have total $b$, their sum is
$$
 \sum_{a=k}^{b-k}\frac{z_p^a z_r^{b-a}}{a(b-a)}.
$$
It is empty when $b<2k$. Otherwise factor out $z_p^kz_r^k$. The remaining unweighted sum over any subinterval has modulus at most $2/|z_p-z_r|$ by telescoping, using $|z_p|,|z_r|\le1$. The weight $1/[a(b-a)]$ is at most $k^{-2}$ and decreases then increases. Its endpoint plus total variation is at most $3k^{-2}$. Summation by parts and $|z_p-z_r|=|p-r|S|z_pz_r|$ give the bound
$$
 \frac{6}{k^2 S}\frac{|z_p z_r|^{k-1}}{|p-r|}.
$$

For the $m=\ell-2$ remaining slots, there are at most $\binom{n}{m}\le n^m/m!$ possible length vectors. Indeed, ordered positive lengths with sum at most $n$ determine $m$ distinct partial sums in $\{1,\ldots,n\}$, and the inverse map is successive differences. This estimate includes $m=0$. Each of the $m$ other factors is bounded by $|z_{p_i}|^{k-1}/k$. After taking the bound for the summed pair, enlarge each assigned set of indices to all assignments with $p\ne r$ on that pair. Use $|p-r|\ge1$ and sum the absolute bounds using $P$. There are $\binom{\ell}{2}$ choices of pair, and $\binom{\ell}{2}/\ell!=1/(2m!)$. Therefore the full contribution from tuples using more than one pole has modulus at most
$$
 \frac{3P^2}{k^2S}\sum_{m\ge0}\frac{(PL)^m}{(m!)^2}
 \le\frac{3P^2}{k^2S}\exp(2\sqrt{PL}).
$$
For the inequality, the sum of the squares of $(\sqrt{PL})^m/m!$ is at most the square of their sum. All estimates involve absolutely convergent pole sums.

Since $L\le(\log n)/100$, the prefactor is $n^{-3/2+o(1)}$ uniformly. More explicitly $P^2=O((\log n)^2)$, $k^{-2}=O(n^{-2}(\log n)^2)$ and $S^{-1}=O(\sqrt{n\log n})$. The exponent satisfies
$$
 2\sqrt{PL}\le 10 L^{3/4}(\log n)^{1/4}
 \le \frac{10}{100^{3/4}}\log n.
$$
The resulting $n^{-3/2+10/100^{3/4}+o(1)}$ is $o(1/n)$, hence $o(d_n)$.

## The sign of the common-pole contribution

First suppose $\theta\ge n^{-2/5}$. The principal pair contributes $2\cos(n\theta)$. For every $|p|\ge3$, split $|z_p|^n=(1+(p^2-1)S^2)^{-n/2}$ into two equal factors. The first is bounded by $\exp(-c n S^2)\le\exp(-c' n^{1/5})$ for absolute positive constants, since $p^2-1\ge8$, $S\le1$, and $S\ge2\theta/\pi$. Summing the second factor over $p$ gives $O(1/S)$ by the preceding integral comparison, using $n/4\ge2$ and $p^2-1\ge p^2/2$. Thus the other poles together give $o(1)$. At a sample the principal pair equals $2(-1)^j$.

For $J\pi/n\le\theta\le n^{-2/5}$ set $B=\lceil(\log n)^2\rceil$. Uniformly on this interval the sum of $|z_p|^n$ over $|p|>B$ is $O(S^{-1}\exp(-c''(\log n)^3))=o(1)$. In the same splitting argument, $(p^2-1)S^2\ge c_0(\log n)^3/n$ by the lower bound on $S$ and $\log(1+x)\ge\min(x/2,\log 2)$ for $x\ge0$. For each retained pole,
$$
 n\,|\arctan(p\tan\theta)-p\theta|=O(n B^3\theta^3)=o(1)
$$
by Taylor expansion, since $B\theta=o(1)$. At a sample $n\theta=j\pi$, each retained conjugate pair therefore has sign $(-1)^j$ because $p$ is odd. The principal pair alone has magnitude two. In both ranges the signed common-pole sum is at least $2-o(1)$. Its coefficient $d_n$ dominates the error from tuples using more than one pole. This proves the signs and the theorem.

## Scope and sources

When $k>n/2$, only single cycles are allowed and the result is the classical real-rootedness of $tA_{n-1}(t)$. The range above also allows the number $\lfloor n/k\rfloor$ of cycles to grow as fast as a constant times $\log n$. The author's discussion supplies the labelled-cycle expansion, a recurrence and computations. An independent public research note on the same excedance family gives additional computation and criteria. The scope comparison found no previous all-root theorem over the growing-cycle-count range stated here. The related ordinary-descent statistic compares neighbors in one-line notation and is treated separately. [Author’s discussion](https://github.com/PerAlexandersson/RealRooted/issues/2590#issuecomment-7059794955) · [Prior exact-family research note](https://raw.githubusercontent.com/1337isnot1337/solved-conjectures/main/docs/alexandersson-long-cycle-research.md) · [Ordinary descents](../long-cycle-descents/README.md)

The proposed theorem has a written proof. No Lean or Rocq proof covers it.
