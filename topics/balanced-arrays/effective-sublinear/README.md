# An explicit logarithmic dimension bound for balanced arrays

**Theorem.** Let $`n,d,r`$ be integers with $`\log n\ge10^6`$, $`d\ge100n/\log n`$, and $`1\le r\le d`$. Write $`a_k`$ for the number of labeled $`n\times d`$ binary matrices with all column sums $`k`$ and every row sum at most $`r`$. Then $`P(q)=\sum_{k=0}^{\lfloor nr/d\rfloor} a_k q^k`$ has exactly $`\lfloor nr/d\rfloor`$ simple negative zeros. Here $`\log`$ is the natural logarithm. [Alexandersson’s conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Author’s issue](https://github.com/PerAlexandersson/RealRooted/issues/2005)

A previous theorem in this repository gives the scale $`Cn/\log n`$ with unspecified constants. This result supplies both constants and an effective bound for the change in the equal-column probability between successive quotas. The all-height conjecture remains open. [Earlier large-dimension theorem](../dense-regime/README.md) · [Eventual theorem in every dimension](../eventual-all/README.md) · [Explicit linear sector at a lower height](../adjacent-quotas/README.md)

**Formal verification**　⬜ None. Two independent agent-assisted reviews check complementary parts of the written proof. [Row expansion and adjacent-quota review](direct-local-review.md) · [Fourier tails and root-count review](direct-global-review.md) · [Manuscript](paper.pdf) · [TeX source](paper.tex)

## Proof

Let $`D=\lfloor nr/d\rfloor`$. To realize every quota $`0\le k\le D`$, assign consecutive blocks of $`k`$ cyclic row labels to the successive columns. Each row is used at most $`\lceil dk/n\rceil\le r`$ times. For $`D\le1`$ the conclusion follows immediately. Otherwise set $`\Gamma_k=a_k^2/(a_{k-1}a_{k+1})`$ at every internal index. The orientation inequality for $`a_k/\binom nk^d`$ yields

$$
\log\Gamma_k\ge d\left(\frac1{k+1}+\frac1{n-k+1}\right)\ge\frac{4d}{n+2}.
$$

At a geometric node $`t_k=\sqrt{a_{k-1}/a_{k+1}}`$ the two first neighboring terms relative to the center have magnitude $`1/\sqrt{\Gamma_k}`$. Further terms decrease outwards by log-concavity. Alternating tails therefore give the strict sign $`(-1)^k`$ at $`-t_k`$ if $`\Gamma_k>4`$. This handles every internal quota when $`d\ge n`$. [Orientation inequality](../orientation-normalization.md) · [Geometric sign bound](../adjacent-quotas/README.md)

Suppose $`d\le n`$ and $`\Gamma_k\le4`$. Put $`u=\log n`$, $`s=d/n`$, $`\delta=100/u`$, and let $`J`$ be the smallest odd integer at least $`2/\delta`$. The displayed orientation inequality gives $`\min(k,n-k)\ge d/\log4-1`$. Since $`J+3<u`$ and $`d/3>u+1`$, all densities within $`J+2`$ indices of $`k`$ lie in $`[s/3,1-s/3]`$ whenever they are feasible.

Put $`U_j=[z^{dj}](\sum_{i=0}^r\binom di z^i)^n`$, $`Q_j=a_j/U_j`$, and $`L_j=[2\pi n (j/n)(1-j/n)]^{-(d-1)/2}`$. For each consecutive feasible pair in this density window the direct row-conditioned comparison gives

$$
\left|\log(Q_{j+1}/L_{j+1})-\log(Q_j/L_j)\right|< n^{-1/8}.
$$

Conditioning on each row size first removes the common row-angle fluctuation from the Fourier integral. The variance of the remaining cubic Gaussian phase is at most $`5/6`$ on regular profiles. This yields a positive lower bound independent of $`s`$, which is needed as the aspect decreases. [Subset cumulants and Taylor bound](direct-row-expansion.md) · [Off-chart estimate](direct-row-tail.md) · [Direct fixed-profile comparison and averaging](direct-comparison.md)

The two immediately adjacent edges are feasible, even if $`k+1=D`$. The log curvature contributed by $`L_j`$ has absolute value at most $`10/(n s^2)`$ by the second derivative of $`\log(x(1-x))`$ on $`[s/3,1-s/3]`$. Consequently $`\log(U_k^2/(U_{k-1}U_{k+1}))<2`$. On the other hand scalar deficit normalization bounds this log curvature below by

$$
\frac{n-1}{(h+1)(h+1+1/s)},\qquad h=nr/d-k .
$$

If $`h\le\sqrt n/2`$, the denominator is at most $`(.6\sqrt n)^2`$, since $`1+1/s\le1+u/100<.1\sqrt n`$. This contradicts the upper bound. Thus $`h>\sqrt n/2`$, so every quota required by the window is feasible. [Scalar deficit inequality](../adjacent-quotas/README.md)

Use the finite theta sign lemma with its parameter $`\lambda_\theta=\delta`$ and tolerance $`\epsilon_\theta=(\delta/4)\exp(-\pi^2/(4\delta))`$. The baseline gives $`\lambda_\theta\le(\log\Gamma_k)/2`$. Also

$$
\log(1/\epsilon_\theta)=\log(u/25)+\pi^2u/400<.04u .
$$

The adjacent slope estimate is smaller than $`\epsilon_\theta/100`$. The scalar local limit estimate and the variance bound for tilted row sizes control the log curvature throughout the window. The explicit sufficient inequalities are $`\sqrt n\ge 10^{12}(J+2)/(\delta^3\epsilon_\theta)`$ and $`n^{1/4}\ge10^{14}/(\delta\epsilon_\theta)`$. Taking logarithms of their right sides gives upper bounds $`36+.08u`$ and $`42+.05u`$, respectively, using $`\log u\le .01u`$. Thus both hold. The theta lemma gives $`(-1)^kP(-t_k)>0`$ at every difficult quota. [Theta sign lemma and scalar estimates](theta-window.md) · [Explicit scalar local limit proof](../adjacent-quotas/scalar.md)

The geometric nodes strictly increase because all internal curvatures exceed one. The signs at these nodes, at zero, and sufficiently far to the left give $`D`$ disjoint negative intervals containing zeros. Since $`P`$ has degree $`D`$, these are all its zeros and each is simple. $`\square`$

## Verification and prior work

Run `python3 -B verify.py` from this directory. It checks the second through fourth subset cumulants by exact enumeration and replays rational inequalities used at the lower cutoff. The theorem quantifies over all inputs in its stated range by the preceding argument.

Canfield, Greenhill and McKay give an asymptotic formula for dense prescribed margins. The repository’s earlier eventual proof develops a related row-subset cumulant expansion. Here the exact fourth-cumulant decomposition, uniform error bounds and adjacent-quota coupling make the height and dimension constants explicit. The recent source search for the original conjecture and its limitations are recorded with the linear-sector proof. [Canfield–Greenhill–McKay](https://doi.org/10.1016/j.jcta.2007.03.009) · [Earlier row-subset expansion](../eventual-all/sparse-fixed-profile-edgeworth.md) · [Dated search record](../adjacent-quotas/README.md) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/2)
