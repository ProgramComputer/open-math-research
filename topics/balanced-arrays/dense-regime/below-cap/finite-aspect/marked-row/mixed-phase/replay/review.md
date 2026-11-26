# Independent review of the mixed-phase sign certificate

Agent-assisted independent proof review and separate arithmetic replay by Codex (`quota_referee`), 2026-11-26.

I checked the mixed-phase extension comparison from the labeled binary-array definition and reconstructed the seven-term sign certificate at the actual geometric radii. The check covers the 809 consecutive quotas $`505662`$ through $`506470`$ for $`(n,d,r)=(10^6,250000,127000)`$. At these radii the polynomial has the strict alternating sign, exactly the indicated number of zeros in the open disk, and no circle zeros. Together with the separately certified lower block and last 95 roots, this yields at least $`506565`$ simple negative roots out of degree $`508000`$. The six-slope example certifies a limitation of the interval test at quota $`507000`$.

## Extension loss and the scalar comparisons

Adding a uniformly chosen unused cell in the designated low column sends the uncapped sampling law to the uncapped sampling law at the next quota. Conditioning on initial legality gives the ratio of the two validity probabilities, since legality after insertion implies legality before insertion. The probability of losing legality is the chance that the chosen row is saturated. Exchangeability across row labels and the fixed number of zeros in the chosen column identify that chance with the saturation probability of one labeled row conditional on having zero in the chosen column.

In that fiber a marked-row mask $`I`$ has completion weight $`F(I)`$ on the other $`n-1`$ rows. Appending one column $`h`$ to $`I`$ decreases its residual quota from $`q_h`$ to $`q_h-1`$. Dividing the two residual binomial normalizations gives $`q_h/(n-q_h)`$. Dividing the two residual validity factors gives the inverse extension factor $`1/(1-e_{mathrm{res}})`$. The residual base has each coordinate in $`[k-1,k+1]`$. Coordinatewise monotonicity of the normalized loss therefore bounds it by balanced losses at $`k-1`$ and $`k+1`$ at the residual height. The total bound $`d(k+2)\le(n-1)r`$, with all coordinates between zero and $`n-1`$, provides positive counts for the required residual bases and their increments. The cyclic block construction applies to unequal column quotas by assigning consecutive blocks of the prescribed lengths around the cycle of rows. It uses every row at most the ceiling of the total divided by the height.

The lower product comparison makes $`F(I)`$ divided by its product weight increasing under inclusion. To check the needed stochastic order between successive weighted-size slices directly, isolate the last item with positive weight $`w`$. Its inclusion probability in a weighted $`j`$-subset is

$$
\frac{we_{j-1}}{e_j+we_{j-1}},
$$

where the elementary symmetric polynomials are on the remaining items. This probability increases in $`j`$ by Newton's inequalities, with the endpoint slices treated as certain. A common uniform variable couples the two inclusion indicators monotonically. Conditional on the indicators, the remaining subset sizes differ by zero or one and can be coupled by identity or induction on the number of items. As a result, the mean of the increasing density on a slice increases with its size. After normalizing over sizes through $`r`$, this gives likelihood-ratio domination and the lower bound on the cap atom. The decreasing ratio for the upper comparison gives the upper bound. The baseline balanced recursion uses the extra factor $`(d-r)/(d(1-K/H))`$ at height $`H`$ and quota $`K`$. The mixed-phase probability has already been conditioned on a specified zero and has no such factor.

For the residual upper tilt I rechecked the matched-mean rule. The marked-row size law divided by the matched truncated binomial has log-concave density ratio by the two-coordinate orientation comparison on the residual quotas. A larger actual top mass would force a single upward crossing with the same mass and a strictly larger actual mean, contradicting the matched mean. The truncated binomial mean is $`dz-z(d-r)Q_r(z)`$, and both its mean and top atom increase with its odds. These facts justify accepting a rational tilt only when the lower enclosure for its truncated mean reaches the target.

## Phase averaging

Let $`m=d-1`$, let $`g`$ be the weighted geometric mean of the two odds, and set $`b`$ to their log ratio. At each size $`j`$ the sum of product weights is at least $`\binom mj g^j`$ by Jensen. The finite-population product mean is bounded above by the $`j`$th power of the one-draw arithmetic mean by Maclaurin's inequality. Hoeffding's lemma for one centered draw of range $`b`$ gives the resulting factor $`\exp(jb^2/8)`$. Since $`j\le r`$ and $`b\le\rho-1`$ for odds ratio $`\rho`$, the ratio between the two cap atoms lies in $`[1-c,(1-c)^{-1}]`$ for $`c\ge r(\rho-1)^2/8`$ and $`c<1`$. Both the numerator and the normalizer obey the coefficient bounds, giving these factors once per top atom. Harmonic and arithmetic odds enclose the geometric odds in the appropriate directions.

For a truncated binomial at log odds $`y`$, its cap atom satisfies $`Q_r''=Q_r[(r-\mu)^2-\mathrm{Var}]`$. The truncated mean is at most the ordinary mean $`mp`$, and the variance is at most $`mp(1-p)\le m/4`$. One direct variance proof conditions a bit to be one or zero. The remaining bits are subject to caps $`r-1`$ and $`r`$ respectively, so their total and each coordinate's mean do not increase when that bit is set to one. Pair covariances are therefore nonpositive. The rational guard using the largest upper odds proves convexity all along both log-odds intervals. Composition with $`u\mapsto-\log(1-au)`$ preserves convexity for each positive factor used and with $`au<1`$. The phase fractions are $`\ell/(d-1)`$ for $`0\le\ell<d`$. Their mean is $`1/2`$, so Jensen gives the lower midpoint and the endpoint chord gives the upper average. Monotone rectangular bounds remain valid whenever the convexity guard fails.

## Shared slope variables and tails

Write $`x_i=S_{k+i}`$, where $`S_h=\log(P_h/P_{h+1})`$, and set $`c_0=(x_{-1}+x_0)/2`$. Relative to the unrestricted geometric node, the log attenuation at positive offset $`j`$ is $`\sum_{i=0}^{j-1}x_i-jc_0`$, and at negative offset $`j`$ it is $`-\sum_{i=j}^{-1}x_i-jc_0`$. This directly yields all six displayed cap factors, with the central first neighbors equal. On the whole interval box checked for a given quota, each successive slope is larger than the previous one. The resulting local magnitudes have at least the unrestricted curvature. For first-neighbor magnitude $`t`$ and subsequent magnitudes $`w_j`$, this implies $`w_{\pm2}\le t^2/G_{k\pm1}<t/2`$ and $`w_{\pm3}<w_{\pm2}`$, using $`t<1`$ and $`G>9/4`$.

The four noncentral partial derivatives of the seven-term parity have signs $`-,+,-,+`$ in order at $`i=-3,-2,1,2`$. The two central derivatives are

$$
\begin{aligned}
\partial_{x_{-1}}&=-t+w_2+\tfrac12w_{-3}-\tfrac32w_3<0,\\
\partial_{x_0}&=t-w_{-2}-\tfrac12w_3+\tfrac32w_{-3}>0 .
\end{aligned}
$$

Thus the same vertex simultaneously minimizes the signed sum over the actual correlated formulas. At the actual array coefficients, log-concavity gives outward decreasing magnitudes. Pairing the tails from even offset four on both sides yields nonnegative terms, with an even final singleton also nonnegative. All the actual internal quotients exceed $`9/4`$, since their logarithms are at least $`4d/(n+2)=n/(n+2)`$ and the replay checks the strict comparison. The sharp disk-count theorem therefore applies to the certified strict signs. Consecutive counts and opposite signs isolate one negative real zero per adjoining annulus, with multiplicity one. [Sharp disk-count theorem](https://github.com/ProgramComputer/open-math-research/blob/8c799d583509ae03f3e3caabc0e3d02449695f15/topics/balanced-arrays/root-distributions/single-sign/README.md)

For the obstruction at $`507000`$, extend the checked synthetic slopes constantly on both ends to the positive support of degree $`508000`$. The resulting validity factors have normalized log-concavity. Zero central curvature contribution gives equal synthetic first neighbors above $`3/5`$. Both second neighbors are below $`(7/50)/8`$, as checked individually. Pairing from odd offset three makes all remaining contributions nonpositive, so the full centered parity is below $`-33/200`$. These synthetic factors suffice to test the interval relaxation, without assuming they come from arrays.

## Independent replay

The separate standard-library checker imports no certificate code. It uses dyadic probability and arithmetic grids, a geometric bound for the omitted downward recurrence, a fixed rational Hoeffding factor $`c=1/3000000`$ checked at each slope, and an alternating series for each negative exponential after division by 16. It reads the primary tilt table as untrusted proposed input, rounds each tilt up to its probability grid, then checks its mean inequality independently. Three independent 32-block phase bounds are compared with the convex bounds. The obstruction tilts are likewise rechecked from the given integer inputs. The independent minimum is at $`506470`$ and exceeds $`0.00215985`$, with all 814 phase-sum enclosures using the convex guard. The different numerical lower bound reflects the deliberately wider uniform Hoeffding factor.

From the mixed-phase directory, run `python3 -IB replay/verify.py`. [Independent checker](verify.py) · [Replay output](output.txt) · [Primary argument and inputs](../README.md)
