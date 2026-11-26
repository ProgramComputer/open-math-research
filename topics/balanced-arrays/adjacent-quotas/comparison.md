# Smoothness of the equal-column probability at consecutive quotas

Suppose $`n\ge 10^{200}`$ and $`n/4\le d\le n`$. Both $`k`$ and $`k+1`$ are feasible, and their densities lie in $`[3/10,7/10]`$. Write $`x=k/n`$, $`v=x(1-x)`$, $`U_k=[z^{dk}](\sum_{s=0}^r\binom ds z^s)^n`$, $`Q_k=a_k/U_k`$ and $`L_k=(2\pi nv)^{-(d-1)/2}`$. Then

$$
\left|\log\frac{Q_{k+1}}{\sqrt d L_{k+1}}-\log\frac{Q_k}{\sqrt d L_k}\right|<10^{-6}.
$$

## Conditional margin probabilities

The scalar law on row profiles $`\ell`$ of total $`dk`$, with each $`0\le\ell_i\le r`$, assigns mass proportional to $`\prod_i\binom d{\ell_i}`$. For each such profile let $`P_\ell`$ be the probability of equal column sums when each labeled row independently chooses a uniform subset of its prescribed size. Put $`H_k(\ell)=P_\ell/(\sqrt d L_k)`$ and $`W_k=\mathbb E H_k=Q_k/(\sqrt d L_k)`$. Tilting the scalar law by $`H_k/W_k`$ gives the law of the row profile of a uniformly random capped array with equal column sums.

Call a profile regular when $`|p_i-x|\le\eta=n^{-1/4}`$ for every $`p_i=\ell_i/d`$. Set $`v_i=p_i(1-p_i)`$, $`A=\sum_i v_i`$, and $`B=\sum_i(p_i-x)^2`$, so $`A=nv-B`$. Write $`b_i=\Pr(\mathrm{Bin}(d,p_i)=\ell_i)`$. The joint Fourier expansion in [the fixed-profile estimate](fixed-profile.md) gives, on regular profiles,

$$
H_k=(1-B/(nv))^{-(d-1)/2}
\prod_i\frac{1}{b_i\sqrt{2\pi d v_i}}\thinspace{}(K_{\bf p}+E_{\bf p}),\qquad
1/100\le K_{\bf p}+E_{\bf p}\le2 .
$$

Here $`K_{\bf p}=\mathbb E(e^{-\Lambda}\cos\Phi)`$ with the Gaussian polynomials defined there. Its explicit Taylor and chart bounds, in the present range, give $`|E_{\bf p}|\le 3\cdot 10^8/\sqrt n`$. Indeed each exponential remainder there is at most $`1/\sqrt n`$ for $`n\ge10^{200}`$, by taking logarithms. The displayed lower bound also holds at exact saturation if the profile is regular.

## Comparing the Gaussian correction

On $`[1/4,3/4]^n`$ the correction satisfies

$$
|K_{\bf p}-K_{\bf p'}|\le10^8\max_i|p_i-p_i'|.
$$

To see this, write $`s=\|{\bf p}-{\bf p'}\|_\infty`$ and use the same independent standard Gaussians $`Z_i,Y_j`$ for both profiles. With $`T_j=Y_j-\bar Y`$, the cell arguments are $`a_i+c_j`$ where $`a_i=Z_i/\sqrt{dv_i}`$ and $`c_j=T_j/\sqrt A`$. These centered Gaussians have precisely the covariance of the joint Fourier quadratic form. Put $`u_i=v_i(1-2p_i)`$, and use bars for averages over rows. Since $`\sum_jT_j=0`$, the three terms in $`-6\Phi`$ are

$$
\begin{aligned}
& d^{-1/2}\sum_i u_i v_i^{-3/2}Z_i^3,\\
& 3\sqrt{n/d}\thinspace{}(d/A)\left(n^{-1/2}\sum_i u_i v_i^{-1/2}Z_i\right)
\left(d^{-1}\sum_jT_j^2\right),\\
& \sqrt{d/n}\thinspace{}\bar u\thinspace{}\bar v^{-3/2}\ d^{-1/2}\sum_jT_j^3 .
\end{aligned}
$$

On this interval $`3/16\le v_i\le1/4`$, $`|v_i'|\le1`$ and $`|u_i'|\le2`$. Thus the factors $`u_i v_i^{-3/2}`$, $`u_i v_i^{-1/2}`$ and $`\bar u\bar v^{-3/2}`$ have Lipschitz constants at most 100 in the indicated supremum distance, by differentiation. The factor $`d/A`$ is at most 6 and has Lipschitz constant at most 30. The first term changes by at most $`100s\sqrt{15n/d}`$ in $`L^2`$, since $`\mathbb E Z_i^6=15`$. In the second term the $`Z`$ and $`T`$ factors are independent and $`\mathbb E(d^{-1}\sum T_j^2)\le1`$. The $`Z`$ factor has $`L^2`$ norm at most 1 and changes by at most $`100s`$ in $`L^2`$. For the last term $`\|d^{-1/2}\sum T_j^3\|_2\le\sqrt6`$ by Wick's identity, since the projection $`I-\mathbf1\mathbf1^\mathsf T/d`$ has zero row sums and the sum of the cubes of its entries is at most $`d`$. These estimates give $`\mathbb E|\Phi-\Phi'|<1000s`$ when $`s>0`$.

For the quartic term, $`\|a_i+c_j\|_4\le10/\sqrt n`$ and $`\|(a_i+c_j)-(a_i'+c_j')\|_4\le100s/\sqrt n`$, from the derivatives of $`v^{-1/2}`$ on the same interval and $`n\le4d`$. The weights $`v_i(6v_i-1)/24`$ are nonnegative, bounded by 1 and vary by at most $`s`$. By Hölder and the fourth-power difference formula, each quartic monomial changes in $`L^1`$ by at most $`4\cdot10^3\cdot100s/n^2`$ before multiplication by its weight. Summing over $`nd\le n^2`$ gives $`\mathbb E|\Lambda-\Lambda'|\le 10^6s`$. The functions $`\cos`$ on the real line and $`e^{-t}`$ for $`t\ge0`$ are 1-Lipschitz and bounded by 1 in absolute value. This proves the stated comparison.

## Coupling the regular profiles

Couple scalar profiles at $`k,k+1`$ coordinatewise in increasing order. For completeness, for independent integer log-concave weights conditioned on total $`m`$, the last coordinate $`S`$ has masses proportional to $`f(s)g(m-s)`$, where $`g`$ is the convolution of the remaining weights. Log-concavity of $`g`$ implies that the last-coordinate distribution at $`m+1`$ stochastically dominates the one at $`m`$ by the increasing likelihood ratio. Log-concavity of $`f`$ likewise shows that the remaining total stochastically increases. Interval supports include their endpoints by contiguous support; equivalently one can use crossed products including zeros. Thus the common-quantile last coordinates satisfy $`S_m\le S_{m+1}\le S_m+1`$. Conditionally couple the remaining profiles by induction, using equality if their totals coincide. Composing $`d`$ successive couplings gives the assertion and $`\sum_i|p_i'-p_i|=1`$.

If both coupled profiles are regular, $`s\le2\eta+1/n\le3\eta`$. The centered displacements have total absolute change at most 2; hence $`|B'-B|\le4\eta`$. Also $`B,B'\le n\eta^2`$. As $`v\ge1/5`$ and $`|v'-v|\le1/n`$, this gives

$$
|B'/(nv')-B/(nv)|\le(20\eta+25\eta^2)/n .
$$

Multiplication by $`(d-1)/2`$ and the derivative bound for $`-\log(1-u)`$ on $`0\le u\le 5\eta^2`$ yield a change below $`50\eta`$ in the logarithm of the first factor of $`H`$.

Robbins' factorial bounds give $`\log(m!)-\log(\sqrt{2\pi m}(m/e)^m)=1/(12m)+e_m`$ with $`|e_m|\le1/(144m^2)`$. Applied to each mean binomial atom, the logarithm of the product in $`H`$ equals $`\sum_i(1/v_i-1)/(12d)`$ with error at most $`n/d^2`$, because $`\ell_i,d-\ell_i\ge d/4`$. Its difference between the two profiles is bounded by $`100\eta+32/n`$. By the lower bound $`1/100`$ and the preceding Lipschitz estimate, the logarithm of the last factor changes by at most $`100(3\cdot10^8\eta+6\cdot10^8/\sqrt n)`$. Combining these three bounds gives $`|\log H_{k+1}-\log H_k|<10^{-8}`$ on the event of joint regularity.

## Removing the regularity condition

The scalar law can be obtained by conditioning independent tilted rows of mean $`dx`$ on total $`dk`$. A single tilted capped binomial is dominated in convex order by $`\mathrm{Bin}(d,x)`$, and the conditioning event has probability at least $`1/(nd+1)`$ by log-concavity and entropy. The proofs apply unchanged to point masses. Consequently the scalar probability of an irregular profile is at most $`t=2n(nd+1)e^{-2d\eta^2}`$. For the actual array, condition on all but two rows. Their size gap has the law of $`2Y-b`$ for $`Y\sim\mathrm{Bin}(b,1/2)`$ conditioned to a symmetric central interval, with $`b\le d`$. If a row differs from $`dx`$ by more than $`d\eta`$, some pair differs by more than $`d\eta`$. Thus the actual irregular-profile probability is at most $`t'=2n^2e^{-d\eta^2/2}`$. [Tail and conditioning proofs](../dense-regime/quantitative-margins.md)

On regular profiles, $`H\le e^{100+10B}`$ by the product formula, the factorial bounds above, and $`-\log(1-u)\le2u`$. Also $`H\ge1/200`$ there: the determinant factor is at least 1 and the factorial estimate bounds the product below by $`e^{-n/d^2}\ge1/2`$. In particular $`W_k\ge1/400`$. For a single unconditioned tilted row put $`Y=(S-dx)/d`$. Integrating $`\Pr(|Y|>z)\le 2e^{-2dz^2}`$ gives $`\mathbb E e^{20Y^2}\le1+40/(2d-20)`$. Independence and conditioning therefore give

$$
\mathbb E_{\rm scalar}[H^2\mathbf1_{\rm regular}]\le (nd+1)e^{500}.
$$

Under the coupled law, the contribution to $`W_k`$ of its own irregularity is at most $`t'W_k`$ by the actual profile bound. Its contribution on own regularity and irregularity of its partner is at most $`\sqrt{t(nd+1)e^{500}}`$ by Cauchy–Schwarz. The same bounds hold with the two quotas interchanged. Since $`d\eta^2\ge\sqrt n/4`$, we have $`t'+400\sqrt{t(nd+1)e^{500}}<10^{-8}`$ for $`n\ge10^{200}`$ (the exponents dominate $`10\log n+500`$ already at the lower endpoint and the difference is increasing). Thus joint regularity accounts for at least $`1-10^{-8}`$ of each $`W`$. Combining with the regular-profile comparison gives the claimed log difference. $`\square`$
