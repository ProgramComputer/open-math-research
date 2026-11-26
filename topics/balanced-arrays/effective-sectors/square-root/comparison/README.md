# Near-full root comparison at the square-root dimension scale

Suppose $d/\sqrt n\to C\in(0,\infty)$, and write $h=d-r$ for the number of holes required in every row. The absolute error of the unrestricted comparison is large at its upper geometric splice. For fixed $h\ge1$, even allowing a global positive dilation of the unrestricted polynomial and a separate complex multiplier on each comparison circle fails as a Rouché strategy in two fixed boundary charts. Here $P(q)=\sum_k a_kq^k$ is the capped polynomial and $F(q)=\sum_{k=0}^n\binom nk^dq^k$ is the unrestricted polynomial. These are limits of comparison methods for the original labeled arrays. The real-rootedness conjecture remains open. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Effective near-full theorem](../README.md) · [Independent review and variance correction](review.md)

## Direct obstruction at unrestricted midpoints

At a fixed hole quota $N$ per column, let $X$ count rows with zero holes. Columns are chosen independently and uniformly. The probability that a specified row has zero holes is $(1-N/n)^d$. For two distinct rows the joint probability is $[((n-N)(n-N-1))/(n(n-1))]^d\le(1-N/n)^{2d}$. Thus $\mathrm{Var}(X)\le\mathbb EX=n(1-N/n)^d$, and $\Pr(X=0)\le1/\mathbb EX$.

Write $-\rho_1,\ldots,-\rho_n$ for the unrestricted roots in increasing order of modulus and set $t=\sqrt{\rho_i\rho_{i+1}}$. For the unrestricted tilt at $t$, the normalized root factors give independent Bernoulli parameters $p_j=t/(t+\rho_j)$. Comparing $p_j$ to the indicator of $\rho_j<t$, using $|p_j-\mathbf1_{\rho_j<t}|\le2p_j(1-p_j)$, gives $|\mathbb EH-(n-i)|\le2\mathrm{Var}(H)$ for the tilted hole quota $H$. If $n-i\sim\alpha d$ with fixed $\alpha>0$, the local mode estimate gives $\mathrm{Var}(H)=O(1)$. The local mode estimate uses only the binomial coefficient ratios. Its argument applies in this aspect ratio. [Midpoint estimates](../refinement-review.md)

On $H\le 2(n-i)$, the conditional probability of no zero-hole rows is $O(1/n)$ because $(1-2(n-i)/n)^d\to e^{-2\alpha C^2}>0$. The discarded probability is $O(1/n)$ by the variance and mean bound. Any proper cap requires absence of zero-hole rows. Hence for the positive modulus of such midpoints, $P(t)/F(t)=O(1/n)$.

In this band the tilted variance is also bounded below. The modal estimate gives $m=n-i+O(1)$ and $\mathbb E(H-m)^2=O(1)$, so a fixed interval about $m$ carries at least half the mass and the modal atom has probability bounded below. The product of the two neighbor weights divided by the square of the modal weight is

$$
\exp\left[-d\left(\log(1+1/m)+\log(1+1/(n-m))\right)\right]
\longrightarrow e^{-1/\alpha}>0 .
$$

Each neighbor weight is at most the modal weight and both neighbors exist eventually. Each thus has probability bounded below. The independent-copy formula gives $\mathrm{Var}(H)\ge\Pr(H=m)\Pr(H=m+1)\ge v_\alpha>0$ for all sufficiently large $n$. The minimum of the normalized unrestricted modulus on $|z|=t$ occurs at $z=-t$ by its negative-root factorization, and

$$
\frac{|F(-t)|}{F(t)}=\prod_j|1-2p_j|
\le\exp\left(-2\sum_j p_j(1-p_j)\right)
\le e^{-2v_\alpha}<1 .
$$

The uniform supremum of $|F(z)-P(z)|/F(t)$ on this circle equals $1-P(t)/F(t)$, because the coefficient losses are nonnegative and the triangle bound is attained at the positive point $z=t$. This supremum tends to one, exceeding the true minimum of $|F(z)|/F(t)$ for large $n$. Thus a uniform absolute coefficient-error comparison cannot certify Rouché in the splice band $n-i\asymp d$. An angle-dependent comparison requires a separate argument.

## Finite occupancy comparison on the exponential scale

Fix $h\ge1$ for the rest of the note. Put $b_N=a_{n,n-N}$ and $Q_h(y)=\sum_N b_N y^N=y^nP(1/y)$. Also set $E_h(z)=\sum_{s\ge h}z^s/s!$ for $z>0$, and let $\mu_h(z)=zE'_h(z)/E_h(z)$ and $V_h(z)=z\mu_h'(z)$ be the mean and variance of the tilted row law.

At hole quota $N$ use $L=dN$ stubs, with $N$ distinguished stubs for each labeled column. Let $E_{h,R}(z)=\sum_{h\le s\le R}z^s/s!$. If a fixed upper row bound $R$ on holes is also imposed, the number of stub allocations, allowing repeated column labels in a row, is $L![z^L]E_{h,R}(z)^n$. A valid binary hole array has $(N!)^d$ such labelings. For each prescribed row occupancy profile with maximum $R$, sample the allocations by uniform permutation over $L$ labeled slots. The expected number of colliding pairs of stubs in one column and one row is at most $d\binom N2(R-1)/(dN-1)=O_R(N)$. At least half the permutations therefore have at most $J=2R(N+1)$ colliding pairs by Markov’s inequality. To fix a repetition of column $c$ in row $j$, swap one involved stub against a slot in a row without column $c$ whose own column does not occur in row $j$. Each of the two restrictions excludes at most $RN$ slots. Since $d>2R$ eventually, a swap exists and reduces the pair count; it preserves row sizes. Deterministic repair has inverse multiplicity at most $\sum_{a=0}^J L^{2a}=\exp[O_R((N+1)\log L)]$. Every assignment at fixed profile has the same slot multiplicity. Thus the fraction of binary allocations is at least $\exp[-O_R((N+1)\log L)]$, uniformly in the profile. For $N=O(n/d)$ this bound has logarithm $o(n)$.

At $dN/n\to\lambda$ with $h<\lambda<R$, the coefficient $[z^{dN}]E_{h,R}(z)^n$ has rate $\log E_{h,R}(z_\lambda)-\lambda\log z_\lambda$, where $`z_\lambda E_{h,R}'(z_\lambda)/E_{h,R}(z_\lambda)=\lambda`$. For the exact total lower bound choose the tilt with mean $dN/n$ at each $n$. Floor the counts of all row sizes above $h+1$, then adjust the counts at $h+1,h$ to achieve the exact total and exactly $n$ rows. Both adjustments cost $O_R(1)$ in the counts. Stirling on this one multinomial type gives $\exp[-O_R(\log n)]$ probability, since all probabilities converge to positive limits. An upper bound one suffices for the rate. With no upper bound, use $E_h$ for the coefficient upper bound at any fixed tilt; use $E_{h,R}$ for the lower bound and then let $R\to\infty$. The saddle solutions converge by uniform convergence on compact tilt intervals, strict increase of the limiting mean, and bracketing of the desired mean.

Consequently, for $dN/n\to\lambda>h$ one has

$$
\frac1n\log\frac{b_N}{\binom nN^d}
\longrightarrow
\psi_h(\lambda)=\lambda\log\lambda-\lambda+
 \log E_h(z_\lambda)-\lambda\log z_\lambda,
\qquad \mu_h(z_\lambda)=\lambda .
$$

For the factorial factors, use Stirling on $(dN)!$ and $(n)_N^d=n^{dN}\exp[o(n)]$. At the feasible endpoint $dN/n\to h$ with $dN\ge nh$, take the profile with $dN-nh=o(n)$ rows of size $h+1$ and the others of size $h$. The same binary repair applies, and even one prescribed row vector has generating coefficient factor with normalized log tending to $-\log(h!)$. The upper bound follows by taking the tilt to zero after the limit. This extends the formula by continuity to $\lambda=h$ on feasible sequences. If $dN<nh$, the capped coefficient vanishes. If $p_h(z)=z^h/(h!E_h(z))$, direct differentiation gives

$$
\mu_h(z)=z+h p_h(z),\qquad z p_h'(z)=(h-\mu_h(z))p_h(z),\qquad
V_h(z)=z+h(h-\mu_h(z))p_h(z)<\mu_h(z).
$$

Hence $\psi_h''(\lambda)=1/\lambda-1/V_h(z_\lambda)<0$. In particular, at three equally spaced hole quotas $N_i=(h+i)\lfloor n/d\rfloor$, $i=1,2,3$, the log coefficient ratios have limiting strictly negative second difference on scale $n$. Any shared multiplier and dilation of the unrestricted polynomial contribute terms affine in $N_i$, so cannot make all three coefficient log errors $o(n)$.

## Positive tilts and failure of scalar circle comparisons

For $y_n(z)=(z/d)^d$ with $z>0$ fixed,

$$
\frac1n\log Q_h(y_n(z))\longrightarrow\log E_h(z),\qquad
\frac1n\log F(y_n(z))\longrightarrow z.
$$

Here $F$ is equal to its own reciprocal. To see the first upper bound directly, multiply the stub count by $(z/d)^{dN}$ and divide by $(N!)^d$. The factor $(dN)!/[(N!)^d d^{dN}]$ is a multinomial probability, at most one. Summing the resulting exponential generating coefficients over $dN$ gives at most $E_h(z)^n$. For the lower bound impose fixed upper $R>h$ and take $N$ nearest to $n\mu_{h,R}(z)/d$. The tilt at this exact mean converges to $z$, and the type estimate and repair give the corresponding lower rate. The multinomial factor has logarithm $-O(d\log(N+1))=o(n)$ by Stirling. Now let $R\to\infty$. The same argument with $h=0$ gives the result for $F$. Related sparse margin asymptotics are used in the earlier fixed-corank sign proof. [Critical-aspect fixed-corank signs](../../../critical-aspect/fixed-corank-critical-upper.md)

The normalized log partitions are convex as functions of $\log z$. Pointwise convergence to differentiable limits implies convergence of derivatives by the bounding secant slopes on either side. Thus at $y_n(z)$ the tilted means, when multiplied by $d/n$, tend to $\mu_h(z)$ and $z$, respectively. The conclusion also holds on sequences of positive $z_n\to z>0$, by monotonicity and bracketing by nearby fixed values. Their variances are $O(1)$ because their modes are $O(n/d)$ and $d\asymp\sqrt n$. More precisely, for either law normalized log-concavity gives the same outward ratio bounds as in the midpoint argument, even though the capped law has a shifted lower endpoint. The mode $m$ satisfies $\mathbb E(H-m)^2\le19(1+m/d)$ and $m\le\mathbb EH+\sqrt{19(1+m/d)}$. For $d\ge10$ this gives $m\le2(\mathbb EH+5)$ and consequently

$$
\mathrm{Var}(H)\le38(1+\mathbb EH/d).
$$

The modal ratio bound uses the orientation theorem. [Normalized log-concavity](../../../orientation-normalization.md)

For a polynomial $A$ of nonnegative coefficients, at positive $y$ its normalized value at $y e^{it}$ is the characteristic function of the tilted exponent law. If that law has mean $m_A$ and variance $v_A$, then

$$
\frac{A(y e^{it})}{A(y)}=e^{itm_A}(1+\varepsilon_A(t)),\qquad
|\varepsilon_A(t)|\le |t|\sqrt{v_A}.
$$

Suppose two such polynomials have mean difference $\Delta_n$ on a circle, with $|\Delta_n|\to\infty$ and $(\sqrt{v_A}+\sqrt{v_B})/|\Delta_n|\to0$. On $0\le t\le 3\pi/|\Delta_n|$, their lifted ratio phase is $t\Delta_n+o(1)$ uniformly. The two error factors stay nonzero because they both tend uniformly to one. For any nonzero complex scalar $c_n$, a point on this arc makes the two values $A(y e^{it})$ and $c_n B(y e^{it})$ opposite in argument, by continuity of the lifted phase over a range longer than $2\pi$. There $|A-c_nB|>|c_nB|$, so a strict Rouché comparison with a scalar multiple of $B$ fails. This applies directly to $A=Q_h$, $B=F$ at each fixed boundary chart, because $\Delta_n\sim (n/d)h p_h(z)$.

## Even a global dilation with matched degrees fails

To compare polynomials of the same degree, put $m_0=\lceil nh/d\rceil$, remove the forced power $y^{m_0}$ from $Q_h$, and remove the $m_0$ smallest-modulus roots from $F$. Write $A$ for the resulting capped polynomial and $F_{\rm tr}$ for the resulting unrestricted product. Scalar normalization of the product is immaterial. Consider any global dilation $B(y)=F_{\rm tr}(\beta_n^d y)$ with $\beta_n>0$ and fix two distinct constants $z_1,z_2>0$.

For $A$ the scaled mean at $y_n(z)$ tends to $\mu_h(z)-h>0$. For finite positive $\beta_n\to\beta$, the corresponding unrestricted count and scaled mean before truncation tend to $\beta z$. Indeed the full unrestricted law is a Bernoulli sum. Its root count up to the radius differs from its mean by at most twice its variance, from $|p-\mathbf1_{p\ge1/2}|\le2p(1-p)$. After removing the $m_0$ smallest moduli, the remaining root count is the positive part of the full count less $m_0$. The same Bernoulli discrepancy bounds the gap between count and truncated mean, with variance at most that of the full law. Thus the scaled mean of $B$ tends to $\max(\beta z-h,0)$. This also holds for $\beta=0$ by monotone comparison with any small fixed positive dilation. These limits cannot match the capped limits for both $z_1,z_2$ since matching a positive limit forces $\beta=\mu_h(z)/z$, and $\mu_h(z)/z=1+h p_h(z)/z$ strictly decreases. At a chart with distinct limits the means differ by order $n/d$ and the variances are bounded, so the scalar circle obstruction applies.

If $\beta_n\to\infty$, the full unrestricted mean multiplied by $d/n$ tends to infinity by monotone comparison with arbitrarily large fixed finite dilations. Removing $m_0=O(n/d)$ Bernoulli factors does not alter this divergence. Its variance is at most $38(1+\mathbb EH_F/d)$, which is $o((\mathbb EH_F)^2)$, so the same small-angle obstruction applies at either chart. Compactness of the positive extended half-line proves that for all sufficiently large $n$ there is no global dilation allowing strict Rouché comparison on both fixed charts, even with separate complex scalars. This argument allows either sign of the mean difference and does not require real-rootedness of the capped polynomial.

A comparison adjusted to the quota would have to change the boundary parameter according to the inverse mean of the conditioned hole law. That relation depends on $z$, so it cannot come from one constant dilation. Control of the corresponding complex fluctuation terms remains open here.

**Formal verification**　⬜ None. An independent agent checked the argument and the correction to the midpoint variance bound. [Review](review.md)
