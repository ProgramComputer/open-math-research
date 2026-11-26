# A finite coefficient inequality sufficient for real-rootedness at a linear dimension bound

**Proposition.** Suppose $n\ge65536$, $200d\ge59n$, and the normalized coefficient curvatures $p_i^2/(p_{i-1}p_{i+1})$ are nondecreasing at all consecutive internal indices of the original balanced-array polynomial. Then it has its full degree of simple negative roots. It suffices to impose monotonicity only from $k-1$ to $k$ at indices where the raw curvature $G_k=a_k^2/(a_{k-1}a_{k+1})$ is at most four. The [finite extension inequality](finite-extensions.md), wherever applicable, would supply the needed monotonicity. For this implication at raw curvature index $k$, the relevant three extension counts are centered at $k-1$.

Write $g_i=((1+1/i)(1+1/(n-i)))^d$ and $m=13/4$. The orientation bound gives $G_i\ge g_i\ge e^{4d/(n+2)}>m$. If $d\ge n$ all signs follow from strict separation. Otherwise $d<n$. Whenever $G_k\le4$, $0.23n<k<0.77n$ by the [explicit sector bound](../effective-sectors/sector-proof.md) since $d\ge n/4$. In particular the three quotas to the left exist. On $[k-1,k]$ the derivative of $\log g$ has magnitude at most $2/(0.228^2 n)$. Monotonicity of $G_i/g_i$ from $k-1$ to $k$ then gives $G_{k-1}\le(1001/1000)G_k$.

Let $x_k=\sqrt{a_{k-1}/a_{k+1}}$. Use the probe $x_k$ if $G_k>4$, and $s x_k$ otherwise, with $s=7/9$. The probes remain strictly ordered, since $x_{k+1}/x_k=\sqrt{G_{k+1}G_k}\ge m>1/s$. At the tilted probe divide $(-1)^kP(-s x_k)$ by $a_k(s x_k)^k$. Its immediate neighbors cost $(s+1/s)/\sqrt{G_k}$. Each side decreases outwards since $1/(s\sqrt{G_k})<1$. All pairs on the right from distance two onward contribute nonnegatively, even if some terms are absent. On the left retain the terms at distances two and three and pair the remaining terms. This gives the lower bound, with $G=G_k$,

$$
1-\frac{s+1/s}{\sqrt G}
+\frac{1}{s^2 GG_{k-1}}
\left(1-\frac1{s\sqrt G\,G_{k-1}G_{k-2}}\right)
\ \ge\ 1-\frac{s+1/s}{\sqrt G}+\frac{B}{G^2},
$$

where $B=(1-1/(s\sqrt m\,m^2))/((1001/1000)s^2)$. The right side stays strictly positive for $G\ge m$. The [accompanying rational checks](curvature-reduction-check.py) replace $B$ by a smaller rational, check positivity at $m$ and verify the derivative is positive thereafter. At the unshifted probes strict factor-four separation gives the required sign. The intermediate value theorem between successive probes and the two endpoint signs supplies all roots.

In particular any counterexample in this dimension range would have two adjacent quotas at which the normalized curvature drops, with raw curvature at most four at the latter quota. The lower slope $59/200$ is a sufficient bound under the stated finite inequality. No optimality assertion is made.
