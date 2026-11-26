# Independent review of the intrinsic root-modulus laws

Agent-assisted mathematical review by Codex (`edge_referee`), 2026-11-26.

I accept the dense, fixed sparse cap, fixed sparse corank, growing sparse cap, and growing sparse corank limits under their respective hypotheses. All roots are counted with multiplicity. The argument uses only positive coefficients and Jensen's formula for their moduli, so the conclusions apply to complex roots. The reciprocal polynomial should retain its forced zero factor when taking the pressure limit. Subtract the forced zeros from its root counts afterward.

## Common finite comparison

For a prescribed profile of row sizes, prescribe all entries outside two columns with margins $`k_a>k_b+1`$. If that partial array has a completion, let $`c`$ be the number of rows forced to receive both entries and $`b`$ the number of rows that must receive one. There are $`\binom b{k_a-c}`$ completions. Replacing the two margins by $`k_a-1,k_b+1`$ increases the binomial coefficient because $`k_a-c\ge k_b-c+2`$. Partial arrays with no old completion contribute a nonnegative count after the change. Repeating the operation decreases the sum of squared margins until all margins are equal whenever the total is $`dk`$. Thus the equal margin vector maximizes the count at each profile. This argument is unchanged for holes or for nonnegative row weights that depend only on row size. I also checked the smoothing inequality by exhaustive enumeration of the profiles for $`d=4`$ and $`n=2,3,4`$.

Let $`R`$ be the equal-column polynomial in the chosen entries, with coefficient $`b_k`$ and degree at most $`n`$. If $`H_i(w)`$ is the scalar row-size polynomial for the $`i`$th row, put $`U_k=[w^{dk}]\prod_i H_i(w)`$. A bound for the number of possible column margin vectors at that total is

$$
C_{n,d}(k)=\min\left((n+1)^d,\binom{dk+d-1}{d-1},\binom{d(n-k)+d-1}{d-1}\right).
$$

The last two bounds count unrestricted weak compositions of the entry or complement totals. Thus $`b_k\ge U_k/C_{n,d}(k)`$. For $`t>0`$, Mahler measure $`M(R(tX))`$ bounds every coefficient by

$$
b_kt^k\le\binom nk M(R(tX)),\qquad M(R(tX))\le R(t).
$$

Indeed the first bound expands the coefficient as an elementary symmetric sum of the roots in $`X`$, each contributing its maximum with one under Mahler measure. The second follows from the triangle inequality on the unit circle and Jensen's formula. This gives the common finite comparison for every selected feasible $`k`$ and $`w>0`$

$$
\frac{U_k w^{dk}}{C_{n,d}(k)\binom nk}\le M(R(w^d X))\le\prod_i H_i(w).
$$

These inequalities include a forced zero of any multiplicity. At $`t=(c_nz)^d`$ and $`u=\log z`$, the log Mahler measure is a constant plus a sum of $`\max(\log t,\log|q_j|)`$ over roots $`q_j`$. Its left and right slopes are $`d`$ times the counts strictly below and at or below $`t`$. Pointwise convergence of convex pressures to a differentiable limit gives convergence of both slopes by secants. Since the counts are monotone in $`z`$ and the limiting counts below are continuous, convergence is locally uniform in $`z>0`$ by a finite grid argument.

## Dense and fixed sparse laws

Write $`H_2(u)=-u\log u-(1-u)\log(1-u)`$. In the dense case use $`w=z`$ and pressure normalized by $`nd`$. Binomial entropy bounds give the row pressure limit $`\sup_{0\le u\le\rho}[H_2(u)+u\log z]`$. For the lower bound take $`k=\lfloor n\min(z/(1+z),r/d)\rfloor`$. Realize the row-size total $`dk`$ using the two consecutive integers bracketing $`dk/n`$, both within the cap. Their weighted product attains the row pressure limit by Stirling, since $`k/n\to\min(z/(1+z),\rho)`$. The smoothing loss is at most $`d\log(n+1)=o(nd)`$, and the Mahler coefficient loss is at most $`n\log 2=o(nd)`$. This is valid for arbitrary relative rates of $`n,d\to\infty`$. The limiting pressure is differentiable in $`\log z`$, including where the maximizer reaches the cap, with derivative $`\min(z/(1+z),\rho)`$. Hence the root count at modulus $`z^d`$, divided by $`n`$, has that limit.

For fixed cap $`r\ge1`$, take $`w=z/d`$ and normalize the pressure by $`n`$. The scalar row polynomial converges to $`E_{\le r}(z)=\sum_{s=0}^r z^s/s!`$. For fixed corank $`h`$, use holes and the analogous scalar row polynomial on $`h\le s\le d`$, which converges to $`E_{\ge h}(z)=\sum_{s\ge h}z^s/s!`$ by domination by the exponential series. For its lower bound first restrict to a fixed $`h\le s\le R`$ with $`R\ge h+1`$, and let $`R`$ grow after taking the limit.

For either bounded size set, the exact positive row weights under tilt converge to positive normalized probabilities. Round their $`n`$-fold type to integer counts with total $`n`$, then modify at most $`d-1`$ rows between two consecutive sizes to make the total size divisible by $`d`$. Both size counts are initially of order $`n`$, so $`d=o(n)`$ ensures that the modifications are possible. The type probability has log $`o(n)`$ by Stirling because every type proportion converges to the corresponding positive tilted probability. Its total $`dk=O(n)`$ gives smoothing loss $`O(d\log(1+n/d))=o(n)`$. The Mahler loss at $`k=O(n/d)`$ is $`O((n/d)\log d)=o(n)`$. Thus the respective pressure limits are $`\log E_{\le r}(z)`$ and $`\log E_{\ge h}(z)`$. The two derivatives are the means of a Poisson variable of parameter $`z`$ conditioned on the indicated size sets.

For the corank use $`Q_h(y)=y^nP(1/y)`$. It has $`m_0=\lceil nh/d\rceil`$ forced zeros and the reciprocals of the nonzero roots of $`P`$. At $`y=(z/d)^d`$, its count, multiplied by $`d/n`$, tends to the conditioned mean. Removing the forced contribution gives the claimed upper root count of $`P`$ at modulus at least $`(d/z)^d`$, with limit equal to the conditioned mean less $`h`$. Stripping the factor before taking the pressure limit would require compensating for the added constant of size $`(dm_0/n)\log d`$ in the normalized pressure.

## Growing sparse cap and corank

Let $`s\to\infty`$, $`s/d\to0`$, and $`L=ns/d\to\infty`$. Take $`w=sz/d`$ and normalize the pressure by $`ns`$. For cap $`s`$, set $`u=\min(z,1)`$ and $`k=\lfloor Lu\rfloor`$. For minimum holes $`s`$, set $`u=\max(z,1)`$ and $`k=\lceil Lu\rceil`$. The chosen floor or ceiling keeps both row sizes bracketing $`dk/n`$ within the permitted range. Each row size $`\ell`$ satisfies $`\ell/s\to u>0`$ and

$$
\log\binom d\ell=\ell\log(d/\ell)+\ell+O\bigl(\log(\ell+1)+\ell^2/d\bigr).
$$

The weighted product of the chosen row counts therefore has log divided by $`ns`$ tending to $`u(1+\log(z/u))`$. The smoothing loss divided by $`ns`$ is $`O(\log(1+L)/L)`$ using the stars-and-bars bound. The Mahler loss divided by $`ns`$ is $`O(\log(d/s)/d)`$ at these indices. Both vanish without an additional aspect-ratio hypothesis.

For the upper bound, the full row sum at $`w=sz/d`$ is at most $`e^{sz}`$. If $`z>1`$ for the cap, or $`z<1`$ for holes, write each weight as the weight at $`s/d`$ times $`z^\ell`$. On the allowed size range, $`z^\ell\le z^s`$. The upper row sum is then at most $`e^s z^s`$. These two bounds match the appropriate lower corner, giving pressure $`z`$ for $`z\le1`$ and $`1+\log z`$ for $`z\ge1`$ in the cap case. For holes, use $`1+\log z`$ for $`z\le1`$ and $`z`$ for $`z\ge1`$. Both pressures are differentiable at one. Jensen therefore gives count divided by $`L`$ tending to $`\min(z,1)`$ at modulus $`(sz/d)^d`$ for the cap. For growing corank, $`\lceil L\rceil`$ forced reciprocal zeros contribute one in the limit. The upper count of original roots with modulus at least $`(d/(sz))^d`$, divided by $`L`$, tends to $`(z-1)_+`$.

## Scope

For the growing cap, the empirical probability law of $`(d/s)|q_j|^{1/d}`$ converges to the uniform distribution on $`[0,1]`$ since the degree is asymptotic to $`L`$. The hole limits describe local upper counts. Their normalization has divergent total mass across all moduli. In the fixed cap case the assumption $`d=o(n)`$ matters. At $`r=1`$ and $`d=n`$, for example, $`P(q)=1+n!q`$, so the single value $`d|q_1|^{1/d}`$ tends to $`e`$ and its count has a step limit. All the modulus laws concern the stated scales and place no condition on the arguments or multiplicities of individual roots.

## Signed supplement on the final manuscript and finite Theorem 4

Codex (`edge_referee`), 2026-11-26. I checked the final TeX manuscript, SHA-256 `7b15bec990155050d3e4accf5f9acca603518c98539ee143164b141f829fbf0e`. Its five limits agree with the statements reviewed above, including both reciprocal scales, the subtraction of the forced reciprocal zeros, and the growth hypotheses on $`d,n,r`$. I accept Theorem 4 for both strict and weak disk counts. [Reviewed manuscript](paper.tex)

For the upper pressure bound, the $`k`$th summand is bounded by $`e^{nd[H(k/n)+v k/n]}\le e^{nd\Phi_p(v)}`$ and at most $`n+1`$ summands are present. Thus the error is precisely bounded by $`U=\log(n+1)/(nd)`$. For the lower bound choose $`k=\lfloor nx\rfloor`$ at a maximizer $`x`$. The bound $`\binom dj\ge e^{dH(j/d)}/(d+1)`$ holds because $`j`$ is a mode of the binomial law of mean $`j`$, including the deterministic endpoints. Concavity and symmetry make $`H(a+t)-H(a)`$ range between $`-H(t)`$ and $`H(t)`$ for $`0\le a\le1-t`$. Both rounding distances are at most $`1/n`$ or $`1/d`$, respectively, and $`H`$ increases on $`[0,1/2]`$. The two rounding costs are therefore $`H(1/n)`$ and $`H(1/d)`$. The row total is exact, so $`B/n`$ is the only cost in the linear term for $`|v|\le B`$. The row-binomial prefactors, margin count, and selected Mahler coefficient contribute at most $`\log(d+1)/d`$, $`\log(n+1)/n`$, and $`\log 2/d`$, respectively. These are all terms in $`E(B)`$.

At $`v`$ both one-sided slopes of $`J`$ lie between its left and right secants of width $`\delta`$. The left slope counts roots strictly inside the radius and the right slope counts roots on or inside, with factor $`1/n`$ in both cases. The upper and lower pressure errors bound the secant comparisons by $`(U+E(|v|+\delta))/\delta`$. The clipped logistic derivative is $`1/4`$-Lipschitz, so either secant of $`\Phi_p`$ differs from $`\Phi'_p(v)`$ by at most the average of $`t/4`$ over $`0\le t\le\delta`$, which is $`\delta/8`$. This gives the stated estimate even when roots lie on the circle or a secant crosses the clipping point.

The publication copy changes the page margins and adds the journal page range. Reverting those two editorial changes reproduces the reviewed source hash.
