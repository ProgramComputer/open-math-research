# An effective sparse-rank bound for balanced binary arrays

Let $a_k$ count labeled $n$ by $d$ binary arrays whose column sums all equal $k$ and whose row sums are at most $r$. Write $D=\lfloor nr/d\rfloor$ and $P(z)=\sum_{k=0}^D a_kz^k$. Assume $n\ge d\ge 2r$ and $\log r\ge32$. Put

$$
L=\frac{\sqrt{r\log r}}8.
$$

Then for every $1\le k<D$,

$$
\frac{a_k^2}{a_{k-1}a_{k+1}}\ge
\left(1+\frac d{d+n(r-L)}\right)^d.
$$

If the right-hand side exceeds four, all $D$ zeros of $P$ are simple and negative. This is a sufficient condition for the balanced-array conjecture in an explicit range. Its effective rank is $r-L$.

**Formal verification**　⬜ None. An independent agent checked the written proof and replayed the exact witness using a separate logarithm enclosure. [Review](review.md) · [Checker](verify.py) · [Replay record](verify-output.txt) · [Prior-art check](literature.md)

## Inputs

The count normalized by $\prod_j\binom n{q_j}$ loses a factor $1-e_i(\boldsymbol q)$ when one raises margin $q_i$. Here $e_i$ is the probability the marked row is full given a zero in column $i$, in the uniform fiber of margins $\boldsymbol q$. This probability is coordinatewise increasing on feasible fibers. The marked-row likelihood comparison for $\boldsymbol q$ and $\boldsymbol q+\mathbf 1$ gives a tilt by $\lambda^J$ in likelihood ratio order, with $\lambda=1+1/k$ when all coordinates of $\boldsymbol q$ are at most $k$. It permits the zero weight imposed on cell $i$. The conditional marked-size law is log-concave with interval support by the equal-margin pairing argument. [Orientation normalization][orientation] · [Marked-row likelihood comparison][likelihood] · [Equal-margin pairing and conditional means][finite]

The published upper-edge row-deficit estimate gives the following inequality in the balanced missing-cell fiber at quota $k-1$. Set $y=d(k-1)/n$, $s=n(r-y)$ and $R=r(d-r)/d$. Its saturation probability $e_0$ satisfies

$$
e_0\ge\frac{(d-r)n}{d(n-k+1)}\frac{n-1}{n+s-1}
\left(1-\left(\frac2R+\frac2r\right)\frac{s(s-1)}{n(n-1)}\right).
$$

This uses the second entry of the minimum in the balanced missing-cell form of the deficit bound. [Upper-edge row-deficit proof][deficit] · [Missing-cell form of the bound][finite]

The likelihood argument and the earlier effective-rank bound are part of [research PR #185](https://github.com/ProgramComputer/open-math-research/pull/185). This follow-up uses its written likelihood inequality and conditional size comparison.

## Curvature from conditional deficits

Coefficients through $D$ are positive by the cyclic block construction. At an internal $k$, compare the paths from equal quota $k-1$ to $k$ and from $k$ to $k+1$ in the same column order. At each phase on the lower path the next column $i$ has quota $k-1$, and all column quotas are $k-1$ or $k$. Let $J$ denote the size of a marked row at this phase, $U=r-J$ its deficit, $\mu=\mathbb E[U\mid X_i=0]$, and $e=e_i(\boldsymbol q)$. Let $e^+$ be the saturation probability for the same missing-cell law on the upper path. All survival probabilities are positive because the next insertion is feasible. Orientation gives $e\ge e_0$.

At fixed $J=j$, a low-quota column is at most as likely to be marked as a high-quota column. To check this, interchange a low mark and a high nonmark in a fixed mask. The residual margins in these two columns become $(k-1,k-1)$ in place of $(k-2,k)$. Fix the other columns and the sum of the two entries in each unmarked row. The row constraints are fixed and the two residual margin counts reduce to binomial coefficients over the singleton positions. Equal quotas maximize that count. Pairing the masks proves the comparison. Low columns are exchangeable, so $\mathbb P(X_i=0\mid J=j)\ge1-j/d$. Since $r-J$ and $1-J/d$ are both decreasing in $J$, their covariance is nonnegative. With $\mathbb EJ\le dk/n$ and $\mathbb P(X_i=0)=(n-k+1)/n$, this gives

$$
\mu\ge (r-dk/n)\frac{n-k}{n-k+1}.
$$

In particular, if $\Delta=r-y\ge2$, then $\mu\ge\Delta/4$ by $d/n\le1$ and $k<n$.

Write $z=1/(k+1)$ and $w=1-z=1/\lambda$. In the conditional law let $T_h=\mathbb P(U\ge h\mid X_i=0)$. The ratios $T_{h+1}/T_h$ decrease on their positive support. Indeed, writing $p_h$ for the mass of $U=h$, the ratio $T_h/p_h$ decreases on the mass support as a sum of products of consecutive decreasing mass ratios. Before that support the tail ratio equals one. Thus $T_{h+m}\le T_hT_m$. For $M=\sum_{h\ge1}w^{h-1}T_h$, summation and the tail comparison give

$$
\mu-M=z\sum_{h,m\ge1}w^{h-1}T_{h+m}\le zM\mu,
\qquad
\mathbb E[w^U\mid X_i=0]=1-zM\le\frac1{1+z\mu}.
$$

Tilt comparison at the largest size gives $e^+\ge e/\mathbb E[w^U\mid X_i=0]\ge e(1+z\mu)$. Consequently $(1-e)/(1-e^+)\ge1+ez\mu$. Also $\mathbb E[w^U\mid X_i=0]\le e+(1-e)w$ because positive deficits are integers. Applying the same tilt bound gives $(1-e)/(1-e^+)\ge [e+(1-e)w]/w=1+e/k$. Thus, restoring binomial curvature after telescoping the $d$ phases,

$$
\left(\frac{a_k^2}{a_{k-1}a_{k+1}}\right)^{1/d}
\ge(1+1/k)(1+h/k)\ge 1+(1+h)/k,
$$

where one may take $h=e_0$ for $\Delta<2$ and $h=e_0\max(1,\Delta/8)$ for $\Delta\ge2$. The factor $1+1/(n-k)$ of the binomial curvature has been dropped here.

## The switching estimate

In the balanced fiber at quota $b=k-1$, let $p_j$ be the probability of size $j$ for an unrestricted marked row. When that row has size $j<r$, choose one of its $d-j$ absent columns, and move a bit from any of the $b$ occupied rows in that column to the marked row. Every donating row stays within the cap since it loses an occupied cell. The marked row starts below the cap and only gains the chosen cell. Every column margin stays fixed. The only rows that change are the marked row and the donor. From a size-$j+1$ array, the inverse chooses a marked bit and an unmarked recipient with zero in its column and row size below $r$. Such a recipient stays within the cap after gaining a bit and the marked row loses one. There are at most $n-b$ zero cells in that column, so the number of inverse choices is at most $(j+1)(n-b)$. Forward and inverse choices correspond bijectively. In particular,

$$
(d-j)b\,p_j\le (j+1)(n-b)\,p_{j+1}.
$$

If $y>r-L$ then $b>0$, and the same switching ensures $p_r>0$. With $x=(d-r)y/(d-y)$ the consecutive inequalities give

$$
\frac{p_{r-u}}{p_r}\le \frac{(r)_{\underline u}}{x^u}
\le \exp\left(uv-\frac{u^2}{2r}\right),
\qquad
v=\log(r/x)+\frac1{2r}.
$$

Here the product uses $\log(1-j/r)\le-j/r$. We have $r-x=d\Delta/(d-y)\le2\Delta\le2L$, so $\log(r/x)\le4L/r$. In the range $\log r\ge32$ this gives $v\le(3/5)\sqrt{\log r/r}$. Completing the square and summing yields

$$
p_r^{-1}\le (1+\sqrt{2\pi r})e^{rv^2/2}\le 4r^{1/2+9/50}.
$$

For the discrete Gaussian bound, keep a maximal grid value separately. For each other integer, bound its value by the integral across the unit interval from that integer toward the maximizing integer, using unimodality and the endpoint heights. Extend the resulting integral to the real line. Column symmetry gives $e_0=(d-r)p_r/(d-y)\ge p_r/2$.

## All indices and root count

Write $t=\log r$. For $y\le r-L$, use $1+h\ge1$. Otherwise $0\le\Delta<L$. We show $h\ge2L/r$, which implies $1+h\ge y/(r-L)$ since $L\le r/2$.

- If $\Delta\ge\sqrt r/4$, then $\Delta\ge2$, and the switching bound gives $h\ge r^{-9/50}/256\ge2L/r$. The last inequality is $e^{8t/25}\ge64\sqrt t$, true at $t=32$ and increasing after division by $\sqrt t$.
- If $\Delta\le\sqrt r/4$, then $R\ge r/2$ and the subtracted term in the deficit estimate is at most $12\Delta^2/r\le3/4$. The first prefactor is at least $1/2$ and the second at least $1/[2(1+\Delta)]$. Thus $e_0\ge1/[16(1+\Delta)]$. For $\Delta\ge2$, use $\max(1,\Delta/8)\ge(1+\Delta)/9$. For $\Delta<2$, use $h=e_0\ge1/48$. This gives $h\ge1/144\ge2L/r$. The last inequality follows from $e^{t/2}\ge36\sqrt t$ at $t=32$ and monotonicity of the ratio thereafter.

Both exponential comparisons at $t=32$ also follow from $\sqrt{32}<6$ and $e^8>384$, using terms of degrees zero through five in the exponential series. Thus $1+h\ge \max(1,y/(r-L))$. Using $k=1+ny/d$ gives $(1+h)/k\ge d/[d+n(r-L)]$, establishing the theorem.

Under the strict factor-four threshold, at geometric radius $t_k=\sqrt{a_{k-1}/a_{k+1}}$ each immediate neighbor has magnitude less than half the central term. Strict log-concavity makes magnitudes decrease outward on both sides. The remaining alternating tails begin with positive terms relative to the central sign and have nonnegative sums. Thus $P(-t_k)$ has sign $(-1)^k$. The radii are strictly increasing by strict log-concavity. With $P(0)>0$ and the sign $(-1)^D$ at sufficiently large negative arguments, these signs isolate $D$ distinct negative zeros, which exhaust the degree and prove simplicity.

## Exact crossover and scope

Run `python3 verify.py` with Python 3 and its standard library. The checker uses $r=2^{48}$, $d=r^2$, and a conservative integer gain $G=2^{23}\le L$. It sets $n$ using a lower rational bound on $\log4$ and verifies the new criterion with $G$, failure of the old $r-1$ criterion, and failure of the unrestricted binomial coefficient-separation test at $k=D-1$. It calculates rational bounds on $\log4$ from the positive series for $4\,\mathrm{atanh}(1/3)$, and uses $u-u^2/2\le\log(1+u)\le u$ for positive $u$. No giant powers are expanded. The check concerns the sufficient criteria and does not compute the coefficients.

An infinite crossover family takes $d=r^2$ and $n$ nearest to $d^2/[(r-L/2)\log4]$. The logarithm of the new lower bound exceeds $\log4$ by order $L/r$, and the old $r-1$ logarithmic bound falls short by that order. At $k=D-1$ the unrestricted log curvature also falls short by order $L/r$, since its correction from $d/(n-k)$ is $O(1/r)$. Here $d$ is of order $n^{2/3}$ and $r$ of order $n^{1/3}$. Consequently the family eventually lies outside the known near-linear and near-full effective sectors, as well as the two restrictions of the rank-dependent theorem. The qualitative eventual theorem does cover this family for sufficiently large unspecified arguments. This proof gives an explicit sufficient criterion and leaves the unrestricted finite conjecture open. [Original conjecture][conjecture] · [Prior $r-1$ criterion][prior] · [Explicit sublinear sectors][sublinear] · [Near-full sectors][sectors] · [Rank-dependent theorem][rank] · [Qualitative eventual theorem][eventual]

[orientation]: https://github.com/ProgramComputer/open-math-research/blob/33e0e399398c10e4455ceda4f430219858ceccc3/topics/balanced-arrays/orientation-normalization.md
[likelihood]: https://github.com/ProgramComputer/open-math-research/blob/33e0e399398c10e4455ceda4f430219858ceccc3/topics/balanced-arrays/marked-row-likelihood/likelihood.md
[finite]: https://github.com/ProgramComputer/open-math-research/blob/33e0e399398c10e4455ceda4f430219858ceccc3/topics/balanced-arrays/marked-row-likelihood/finite.md
[deficit]: https://github.com/ProgramComputer/open-math-research/blob/33e0e399398c10e4455ceda4f430219858ceccc3/topics/balanced-arrays/dense-regime/below-cap/finite-aspect/upper-edge/paper.tex
[prior]: https://github.com/ProgramComputer/open-math-research/blob/33e0e399398c10e4455ceda4f430219858ceccc3/topics/balanced-arrays/marked-row-likelihood/curvature.md
[sublinear]: https://github.com/ProgramComputer/open-math-research/blob/33e0e399398c10e4455ceda4f430219858ceccc3/topics/balanced-arrays/effective-sublinear/README.md
[sectors]: https://github.com/ProgramComputer/open-math-research/blob/33e0e399398c10e4455ceda4f430219858ceccc3/topics/balanced-arrays/effective-sectors/README.md
[rank]: https://github.com/ProgramComputer/open-math-research/blob/33e0e399398c10e4455ceda4f430219858ceccc3/topics/balanced-arrays/dense-regime/rank-dependent/README.md
[eventual]: https://github.com/ProgramComputer/open-math-research/blob/33e0e399398c10e4455ceda4f430219858ceccc3/topics/balanced-arrays/eventual-all/README.md
[conjecture]: https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays
