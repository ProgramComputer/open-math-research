# Explicit small ranks for fixed minimum cycle length

For fixed $k\ge3$, let $E_{n,k}(t)=\sum_p a_{n,p}t^p$ count permutations with all cycles of size at least $k$ by excedances, and put $P_n(t)=E_{n,k}(t)/t$. The elementary results below give simple negative roots and strict consecutive order at all ranks $h\le(3/8)\sqrt n$ for $n\ge\max(400,25k^2)$. These signs meet the [principal-pole estimates](fixed-threshold.md) at the ranks used there.

## Coefficients at the overlap

Cut the cycles at every ascent into $p$ labeled decreasing runs. A color word on $[n]$ assigns the labels to the runs, and a permutation of the runs specifies the upward boundary edges. Acceptance requires nonempty run classes, each boundary upward, and the total label count in each run-cycle at least $k$. Every admissible permutation has exactly $p!$ choices of run labels, canceled by the $p!$ possible uniform permutations of runs. Thus $\alpha_{n,p}=a_{n,p}/p^n$ is the acceptance probability, with $0\le\alpha_{n,p}\le1$. The run encoding is the one in the [reviewed extreme-rank proof](https://github.com/ProgramComputer/open-math-research/pull/7).

For $n\ge\max(400,25k^2)$ and $p\le(3/5)\sqrt n$, require each color to occur at least $k$ times in the full word and at least once in each half. Then every run permutation is accepted. The full-word count of one color is binomial of mean $\mu=n/p\ge(5/3)\sqrt n>8k$. Its probability below $k$ is at most $\exp(-49\mu/128)$ by the lower-tail bound. The shorter half has mean at least $(4/5)\sqrt n$, so its empty-color probability is at most $\exp(-4\sqrt n/5)$. The union bound gives
$$
1-\epsilon_n\le\alpha_{n,p}\le1,\qquad
\epsilon_n=\frac95\sqrt n e^{-3\sqrt n/5},\qquad
\sqrt n\,\epsilon_n<\frac1{100}.
\tag{1}
$$
The last expression decreases for $n\ge400$ and satisfies the bound at $n=400$ since $e>13/5$. The same interval contains $\alpha_{n+1,p}$ for these $p$, as $\epsilon_{n+1}\le\epsilon_n$.

## Exact first ranks and their consecutive signs

For $1\le h\le(3/8)\sqrt n$, let
$$
u_{n,h}=\left(\frac h{h+1}\right)^n,\qquad
F_{n,h}(z)=\frac{E_{n,k}(u_{n,h}z)}{h^n u_{n,h}^h z^h}
=\sum_{p\ge1}\alpha_{n,p}
\left[\frac ph\left(\frac h{h+1}\right)^{p-h}\right]^n z^{p-h}.
$$
Coefficients beyond the degree are zero. Both bases at $p=h,h+1$ equal one. In the normalized bracket raised to $n$, successive terms away from this pair in either direction decrease by a ratio at most $q=e^{-5}<1/100$. Indeed the maximal ratios on the left and right are $(1-1/h^2)^n$ and $(1-1/(h+1)^2)^n$, respectively, and $n/(h+1)^2>5$ when $n\ge400$. The first ratio is unnecessary when $h=1$.

On $1/2\le|z|\le3$,
$$
|F_{n,h}(z)-(1+z)|\le4\epsilon_n+
\frac{2q}{1-2q}+\frac{9q}{1-3q}<\frac12 .
$$
On the circle $|z+1|=1/8$ the same bound with $|z|\le2$ gives $3\epsilon_n+6q/(1-2q)<1/8$. Rouché on the circles of radii $1/2$ and $3$ after multiplying by $z^{h-1}$ gives respectively $h-1$ and $h$ zeros of $P_n(u_{n,h}z)$. Rouché on the small offset circle gives a simple real negative root, since the disk is conjugation invariant. This establishes its absolute rank $h$, and its modulus belongs to $(7u_{n,h}/8,9u_{n,h}/8)$.

At such a root $t=u_{n,h}z$, consider $E_{n+1,k}(t)-hE_{n,k}(t)$ divided by $h^n u_{n,h}^h z^h$. The coefficient of each normalized term is then
$$
(p-h)\alpha_{n,p}+p(\alpha_{n+1,p}-\alpha_{n,p}).
$$
The $p-h$ part vanishes at $p=h$ and at $p=h+1$ contributes $\alpha_{n,h+1}z$, strictly below $-(7/8)(1-1/100)$. With $s=1/50$, the sum of absolute values of its remaining terms is at most
$$
\sum_{\ell\ge1}\ell s^\ell+2\sum_{\ell\ge1}(\ell+1)s^\ell
=\frac{3s}{(1-s)^2}+\frac{2s}{1-s}<\frac{11}{100}.
$$
For $p\le(3/5)\sqrt n$, (1) bounds the coefficient increment by $p\epsilon_n<3/500$. The absolute sum of the normalized bracket terms is less than four, so this portion contributes less than $3/125$. For $p>(3/5)\sqrt n$, one has $p-h>(9/40)\sqrt n\ge4.5$ and $p<3(p-h)$. The increment bound $p$ then gives a total less than $6\sum_{\ell\ge4}(\ell+1)s^\ell<1/1000$. The result is therefore strictly negative. Restoring the normalization, $E_{n+1,k}$ at the old root has sign $(-1)^{h+1}$ and $P_{n+1}$ has sign $(-1)^h$.

At the old root the modulus divided by $u_{n+1,h}$ lies in $(7/8,9/4)$, since $u_{n+1,h}/u_{n,h}=h/(h+1)$. This lies strictly inside the new annulus $(1/2,3)$, which has only its rank-$h$ root and exactly $h-1$ simple negative roots inside its lower boundary. Therefore the new sign puts the old rank $h$ strictly after the new rank $h$ and strictly before all larger new ranks.
