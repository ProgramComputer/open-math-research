# An explicit finite reduction to quotas near the row cap

**Partial theorem.** Suppose $n\ge1024$, $n/4\le d\le n$, $1\le r<d$, and $n/5\le k\le4n/5$. Put $h=1/n$ and

$$
\delta=\frac rd-\frac{k+2}{n}.
$$

If $\delta\ge\sqrt{8\log n/d}$, the simultaneous extension counts satisfy $2u_k>u_{k-1}+u_{k+1}$. In particular all three counts in the conclusion are defined. This is a finite assertion at varying rank and dimension.

**Consequence.** Suppose $n\ge65536$, $59n/200\le d<n$, and $1\le r<d$. If the original array polynomial has a nonreal root, there must exist an internal quota $j$ with $G_j\le4$ for which

$$
\frac{nr}{d}-j < 1+n\sqrt{8\log n/d},
\qquad
\frac{G_{j-1}}{g_{j-1}}>\frac{G_j}{g_j}.
$$

Here $G_j=a_j^2/(a_{j-1}a_{j+1})$ is the raw curvature and $g_j=((1+1/j)(1+1/(n-j)))^d$. The [tilted sign criterion](https://github.com/ProgramComputer/open-math-research/blob/27e3e70d6603e8a395c5fdb7ff944922bce83380/topics/balanced-arrays/engset-curvature/curvature-reduction.md) gives a quota with both the curvature drop and $0.23n<j<0.77n$. If the distance inequality failed, the theorem at $k=j-1$ would imply the opposite curvature comparison by the extension argument. This locates a necessary failure of a coefficient inequality; it does not locate a nonreal root in the complex plane.

[Independent review](rare-overflow-strip-review.md)

## Bounding the error by two joint row events

At quota $i$, let $T_i=T(i/n)$ with $T(z)=\Pr(\mathrm{Bin}(d,z)>r)$. Write $p_i=a_i/\binom ni^d$. The first two Bonferroni bounds give

$$
1-nT_i\le p_i\le1-nT_i+\tbinom n2 T_i^2.
$$

For the upper bound, conditional on the first row's full indicator vector, the second row's entries are independent across columns. Each conditional success probability decreases from $i/(n-1)$ to $(i-1)/(n-1)$ upon changing the first row's corresponding entry from zero to one. Thus the conditional second-row overflow probability is a decreasing function of the first-row indicators. Their law is a product. An increasing and a decreasing function on a product of Bernoulli variables have nonpositive covariance, by induction conditioning on the last variable. The joint overflow probability is at most $T_i^2$.

Let $T_*=T((k+2)/n)$. Exponential Markov's inequality, or the entropy bound $H(a,b)\ge2(a-b)^2$, gives $T_*\le e^{-2d\delta^2}\le n^{-16}$. In particular $nT_*<1/2$. For the four quotas from $k-1$ to $k+2$, the preceding bounds imply $|\log p_i+nT_i|\le2n^2 T_*^2$; use $-\log(1-v)-v\le v^2$ for $0\le v\le1/2$ and $\log(1-v+w)\le-v+w$. By coupling nested column subsets, $p_i$ decreases with $i$. For $i=k-1,k,k+1$, it follows that $A=d^{-1}\log(p_{i+1}/p_i)$ is nonpositive and $|A|\le2nT_*/d$ (use $p_{i+1}\ge1-nT_*$ and $p_i\le1$). Since $0\le e^A-1-A\le A^2/2$,

$$
\left|u_i-(n-i)+\frac{n(n-i)}{d}(T_{i+1}-T_i)\right|\le 6n^3T_*^2/d.
$$

## A strictly convex binomial-tail increment

Write $F=T'$. Direct differentiation gives $F(z)=d\binom{d-1}r z^r(1-z)^{d-r-1}$. On $[(k-1)/n,(k+2)/n]$ both coordinates $z,1-z$ exceed $0.19$. The logarithmic derivative

$$
B(z)=\frac{r-(d-1)z}{z(1-z)}
$$

satisfies $4d\delta\le B\le6d$, and $|B'|\le 28d$. Also $B^2\ge128 d\log n\ge 56d$, and $B>40$. For $z$ from $(k-1)/n$ to $(k+1)/n$, put $f(z)=(1-z)(T(z+h)-T(z))$. Differentiating under this one-step integral yields

$$
f''(z)=\int_0^h F(z+t)\big[(1-z)(B(z+t)^2+B'(z+t))-2B(z+t)\big]dt
\ \ge\ \tfrac1{25}h(4d\delta)^2 F_{\min}.
$$

Indeed $(0.19/2) B^2-2B\ge B^2/25$ for $B\ge40$. As $B$ is decreasing on $(0,1)$, integration of the tangent bound for $\log F$ to the left of $z_*=(k+2)/n$ gives $T_*=\int_0^{z_*}F(z)dz\le F(z_*)/B(z_*)$. Also $F_{\min}\ge e^{-18}F(z_*)$, since the interval length is $3/n$ and $B\le6d$. Integrating $f''$ against the central second-difference kernel of total mass $h^2$ gives

$$
f((k-1)/n)-2 f(k/n)+f((k+1)/n)
\ge 10^{-8} h^3 (d\delta)^3 T_*.
$$

Here $64e^{-18}/25>10^{-8}$. This supplies a positive leading term of size at least $10^{-8} (n^2/d)(d\delta/n)^3 T_*$ in $2u_k-u_{k-1}-u_{k+1}$. The combined absolute error in the three extensions is at most $24n^3 T_*^2/d$. It is smaller than the leading term, since $d/n\ge1/4$, $\delta>n^{-1/2}$, and $nT_*\le n^{-15}$ give $24\cdot64\cdot10^8<n^{27/2}$ for $n\ge1024$. This proves the theorem.
