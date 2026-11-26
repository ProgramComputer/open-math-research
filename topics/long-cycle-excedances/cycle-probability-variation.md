# Cancellation between the two nearest Eulerian poles at arbitrary cycle count

Let $k\ge3$ and put $d_0=1$, $d_m=0$ for $1\le m<k$. For $m\ge k$, $d_m$ denotes the probability that a permutation on $m$ letters has all cycles of length at least $k$. Write $D(z)=\sum_m d_m z^m=\exp(\sum_{j\ge k}z^j/j)$. The Eulerian pole expansion of an allowed cycle gives the coefficient identity
$$
\sum_{n\ge0} F_n(\theta)u^n=\prod_{p\text{ odd}}D(z_pu).
$$
The sum of absolute values of the logarithmic coefficients converges for each power since the permitted lengths are at least three. The two factors $p=\pm1$ alone contribute $2d_n\cos(n\theta)$ and the mixed term
$$
M_n=\sum_{j=k}^{n-k}d_jd_{n-j}\exp(i(n-2j)\theta).
$$

**Lemma.** For every $k\ge3$,
$$
\sup_{m\ge k}d_m\le1/k,\qquad \sum_{m\ge k+1}|d_m-d_{m-1}|<1/k.
$$
Furthermore $d_m\ge1/(2k-1)$ for every $m\ge k$.

Indeed $m d_m=\sum_{j=0}^{m-k}d_j$ using logarithmic differentiation. For $k\le m<2k$ this gives $d_m=1/m$. The two pointwise bounds then follow by induction using the sum of one plus the $m-2k+1$ possible nonzero terms of positive index when $m\ge2k$.

Let $\Delta_m=d_m-d_{m-1}$ and $b=1/k-1/(2k-1)$. For $m\ge k+1$, $m\Delta_m=d_{m-k}-d_{m-1}$. Hence $\Delta_{2k}=b/(2k)$ and the variation between $k$ and $2k$ is $b(1+1/(2k))$. For every $m\ge2k+1$ we have $m|\Delta_m|\le\sum_{i=m-k+1}^{m-1}|\Delta_i|$. Summing to any finite $M$ and counting the at most $k-1$ appearances of each index bounds the tail by $(k-1)/(2k+1)$ times the entire variation from $k$ to $M$. Consequently the total variation is at most
$$
\frac{2k+1}{k+2}\left(1+\frac1{2k}\right)\left(\frac1k-\frac1{2k-1}\right)<\frac1k .
$$
The last inequality is equivalent to $(2k+1)^2(k-1)<2k(2k-1)(k+2)$.

Extend $g_m=d_m$ for $m\ge k$ by zero elsewhere. Its total variation on the integers is less than $2/k$. For $b_j=g_jg_{n-j}$ we therefore have $\sum_j|b_j-b_{j-1}|<4/k^2$. Multiplication by $(n-2j)/n$ adds at most $(2/n)\sum_j b_j\le2/k^2$ to this bound, since the support lies within $[0,n]$. Discrete summation by parts with $|1-e^{2i\theta}|=2\sin\theta$ gives
$$
|M_n|\le\frac2{k^2\sin\theta},\qquad |M_n'|/n\le\frac3{k^2\sin\theta}.
$$
Thus the nearest-pole mixed terms admit an effective cancellation bound independent of the number of permitted cycles.

An absolute sum alone cannot give this result. Before the $j$-phase cancellations, the ratio of mixed mass to single-phase amplitude is at least $k(n-2k+1)/(2(2k-1)^2)$ for $n\ge2k$, by the two pointwise bounds. This grows without bound when $n/k$ does. To use the lemma in a proof of the original conjecture, the other poles and the overlap with the smallest roots must also be controlled. Prior work in this repository already uses oscillatory estimates on cycle compositions; the comparison here takes place after summing all permutations assigned to each of the two principal poles.

A second obstruction to absolute summation occurs already for two occupied poles, one principal and one nonprincipal. Take $\sin^2\theta=1/n$ and retain $p=1,3$. The absolute mass from using each pole at least once is at least $e^{-4}(n-2k+1)/(2k-1)^2$, because $|z_3|^j=(1+8/n)^{-j/2}\ge e^{-4}$ for $k\le j\le n-k$. Its ratio to $d_n$ can be arbitrarily large. Effective control in this regime must keep the phase difference or replace this comparison.

For a fixed nonprincipal $p$ and a principal pole $a\in\{-1,1\}$, set $\eta=z_p/z_a$. Factoring $\eta^k$ before summation by parts gives
$$
\left|\sum_{j=k}^{n-k}d_jd_{n-j}z_p^j z_a^{n-j}\right|
\le\frac{4|z_p|^{k-1}}{k^2|p-a|\sin\theta},
$$
since $|1-\eta|=|p-a|\sin\theta |z_p|$. This proves cancellation for that pair at every positive angle. Terms involving three or more distinct poles remain. The scalar sequence $d_n$ is also treated, with sharper asymptotic information, in Robertas Petuchovas’s 2016 paper on permutations without short cycles. The present argument needs a uniform discrete variation estimate for oscillatory sums. [Petuchovas, May 9, 2016](https://arxiv.org/abs/1605.02690)
