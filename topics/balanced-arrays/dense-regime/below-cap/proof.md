# Almost all zeros below the row cap

This theorem addresses a range of Per Alexandersson’s balanced-array conjecture for uniform matroids. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

Let $P(q)=\sum_{k=0}^D a_kq^k$ be the labeled balanced-array polynomial with $n$ rows, $d$ columns, row cap $r$, and $D=\lfloor nr/d\rfloor$. Let $S(P)$ count its simple strictly negative zeros.

**Theorem.** There is an absolute constant $C$ such that, for $2\le d\le n$ and every $1\le r\le d$,

$$
0\le D-S(P)\le C D \frac{\sqrt{n\log(n+1)}}{d}.
$$

In particular, along any sequence where $d/\sqrt{n\log(n+1)}\to\infty$, the fraction of simple negative roots tends to one uniformly over caps whenever $D>0$. Dimensions $d>n$ already have all roots by coefficient separation. The estimate leaves open whether any of the remaining roots are nonreal or repeated.

The proof identifies individual zeros in the range where the estimate is informative. Write $F(q)=\sum_{k=0}^n\binom nk^d q^k$ for the unrestricted polynomial and $-\rho_1,\ldots,-\rho_n$ for its zeros in increasing order of absolute value. For $D>d/2$, every index

$$
1\le i\le (1-\alpha)D,\qquad
\alpha=A\frac{\sqrt{n\log(n+1)}}{d}\le\tfrac12
$$

gives a distinct simple zero of $P$ in $|z+\rho_i|<\rho_i/(4n^2)$, for an absolute constant $A$ sufficiently large. These are the first $i$ capped zeros in order of increasing modulus up through any accepted index $i$. Every other capped zero has modulus greater than $T_i=\sqrt{\rho_i\rho_{i+1}}$.

## Counting arrays on a root circle

At the positive radius $t=|z|$, give the integer $K$ weights $\binom nk^d t^k/F(t)$. Given $K=k$, choose $d$ independent, uniform $k$-subsets of the $n$ rows. Each outcome is exactly one unrestricted labeled matrix. Thus

$$
\frac{|P(z)-F(z)|}{F(t)}
\le\frac{F(t)-P(t)}{F(t)}
=\mathbb P(\text{at least one row exceeds the cap}).
$$

Given $K=k$, the sum in any specified row has the binomial law with $d$ trials and success probability $k/n$.

The [root-circle estimate](full-rank-root-stability.md) gives a log-spacing of at least $2\pi/\sqrt{n(n+1)}$ for the full polynomial and the lower bound

$$
\frac{|F(z)|}{F(t)}
\ge \exp[-C_1(1+\mathrm{Var}(K))\log(n+1)]
$$

on $|z+\rho_i|=\rho_i/(4n^2)$. The disks are pairwise disjoint. Write $p_j=t/(t+\rho_j)$. The factorization of $F$ shows that $K$ has the law of a sum of independent Bernoulli variables with parameters $p_j$. By the spacing, the number of $\rho_j\le t$ is $i$ or $i-1$. Each discrepancy between $p_j$ and $\mathbf1_{\rho_j\le t}$ is at most $2p_j(1-p_j)$, so $|\mathbb E K-i|\le1+2\mathrm{Var}(K)$.

## Local variance and cap error

Here are details keeping the root count uniform when $r$ is small. If $m$ is a mode of $K$, then

$$
\mathbb E(K-m)^2\le C_2(1+m/d).
$$

Indeed the weights are $b_j=\binom nj^d t^j$. At distance $j$ to the right of $m$, their next outward ratio is at most $((m+1)/(m+j+1))^d$, by comparison with the right-hand ratio at the mode. The left-hand counterpart is at most $((m-j)/m)^d$ if $j<m$ and $m>0$. Omit unavailable sides. Put $L=1+\lceil\sqrt{(m+1)/d}\rceil$. For $j\ge L$ these bounds are at most $\exp(-c/L)$: on the right use $\log(1+L/(m+1))\ge L/(m+1+L)$ and $dL^2\ge m+1$, and on the left use $\log(1-L/m)\le-L/m$ when applicable. Shifting a tail index outward by $hL$ steps therefore reduces its mass by at least a factor $e^{-ch}$ for indices already at distance $L$ or more. Summing gives $\mathbb P(|K-m|\ge(h+1)L)\le2e^{-ch}$ and hence the moment bound.

Consequently $|m-i|\le C_3(1+m/d)$, by the preceding mean-index estimate and Cauchy–Schwarz. We may take $d\ge2C_3$ in the nontrivial range by enlarging $A$. Then $m\le C_4(i+1)$. Since $i\le D$ and $D>d/2$, we have

$$
\mathrm{Var}(K)\le C_5D/d,\qquad
|\mathbb E K-i|\le C_6D/d.
$$

Let $s=\alpha D$. For $A$ sufficiently large, $\mathbb E K\le D-3s/4$, since $i\le D-s$ and $\alpha d=A\sqrt{n\log(n+1)}$. Bernstein's inequality for the Bernoulli sum therefore gives $\mathbb P(K>D-s/2)\le\exp(-c_1s^2/D)$. Indeed the variance is $O(D)$ and the threshold above the mean is at least $s/4$, with $s\le D$. On the complementary event the expected sum in a specified row is at most $d(D-s/2)/n$, whereas $r\ge dD/n$. A binomial upper-tail bound at the gap $ds/(2n)$ gives probability at most $\exp(-c_2ds^2/(nD))$: both the mean and the chosen gap are bounded by $dD/n$. The union bound over rows and $d\le n$ give

$$
\frac{|P(z)-F(z)|}{F(t)}
\le (n+1)\exp[-c_3A^2(D/d)\log(n+1)].
$$

Because $D/d>1/2$, this is strictly smaller than the lower bound for $|F(z)|/F(t)$ once $A$ is a large enough absolute constant. Rouché's theorem gives exactly one zero counting multiplicity in each indicated disk. Conjugation preserves the disk and the polynomial is real, so that zero is real, simple and negative.

To prove ordering, fix an accepted $i$, necessarily $i<n$, and take $t=T_i=\sqrt{\rho_i\rho_{i+1}}$. Exactly $i$ of the unrestricted moduli are below $t$, so the Bernoulli mean-index, local variance and cap-error bounds apply unchanged on the full circle $|z|=t$. The log-distance from $t$ to each unrestricted modulus is at least $\pi/\sqrt{n(n+1)}$. The close and far factor estimates in the [root-circle bound](full-rank-root-stability.md), now with no centered factor, give $|F(z)|/F(t)\ge\exp[-C_7\mathrm{Var}(K)\log(n+1)]$ there. Increasing the same absolute $A$ if necessary gives strict Rouché dominance on this circle. Thus $P$ has exactly $i$ zeros inside it and none on it. By spacing, $\rho_i(1+1/(4n^2))<T_i$, so the first $i$ small disks lie entirely inside this circle and exhaust its capped zeros. The disk order is also their modulus order, since their modulus intervals are pairwise disjoint. This proves the ordering assertion.

## Completing the uniform estimate

If $D\le d/2$, all internal coefficient ratios $a_k^2/(a_{k-1}a_{k+1})$ exceed four by the normalized log-concavity bound $(1+1/k)^d(1+1/(n-k))^d$. Indeed $(1+2/d)^d\ge4$ for $d\ge2$. The geometric-center sign argument gives all $D$ simple negative roots, including the immediate cases of degrees zero and one. For $d>n$ the same conclusion follows from $(1+2/n)^{2d}>4$ at every internal index. Both inequalities follow from the [published orientation comparison](../../orientation-normalization.md).

In the remaining case, if $\alpha>1/2$, the trivial bound $D-S(P)\le D$ is sufficient after increasing $C$. Otherwise the disks supply at least $\lfloor(1-\alpha)D\rfloor$ simple negative roots, so the loss is at most $\alpha D+1$. Here $\alpha D>A\sqrt{n\log(n+1)}/2$, which absorbs the integer rounding. This proves the theorem.
