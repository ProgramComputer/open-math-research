# Independent review of the multiplicative cap-probability bound

Agent-assisted mathematical review by Codex (`edge_referee`), 2026-11-26.

I accept the marked-row conditional saturation bound and its transfer to geometric-circle signs. The sign test uses only a scalar truncated-binomial boundary atom. It does not require the cap event to have appreciable probability. I independently reproduced the finite cutoff at quota $`504158`$ in the million-row example.

## Exact conditional row bound

For a proper cap $`1\le r<d`$, let $`p_k=a_k/\binom nk^d`$. At a feasible balanced quota $`K\ge1`$, prescribe the mask $`I`$ of one labeled row. The remaining $`n-1`$ rows have quotas $`K-1`$ in $`I`$ and $`K`$ elsewhere. The count $`F_j`$ of completions depends only on $`j=|I|`$ by column symmetry. Its positive support has no gap, since reducing any quota preserves feasibility. The cross-coordinate orientation comparison gives $`F_j^2\ge F_{j-1}F_{j+1}`$ by increasing either of two coordinates from $`K-1`$ to $`K`$ in the same lower fiber. The marked-row degree masses are proportional to $`\binom d j F_j`$ on $`0\le j\le r`$. [Orientation comparison, equation (4)](https://github.com/ProgramComputer/open-math-research/blob/14a7c082563830be7b42e5353c2269944a4260b5/topics/balanced-arrays/orientation-normalization.md)

Suppose $`0<dK/n<r`$. There is a unique binomial parameter $`z_*`$ such that the binomial distribution truncated to $`[0,r]`$ has mean $`dK/n`$. This follows by differentiating the mean with respect to log odds, obtaining the positive variance. The actual marginal row degree has that same mean by row exchangeability. The ratio of its masses to the truncated binomial masses is log-concave, because the binomial factor cancels and the remaining tilt is geometric in $`j`$. Its superlevel set at one is an interval. If the actual mass at $`r`$ exceeded the binomial mass there, the signed mass difference would have a negative prefix and a positive suffix. The equal total mass would then give strictly greater mean, a contradiction. Thus the actual saturation probability is bounded above by $`q_r(z_*)=\Pr(\mathrm{Bin}(d,z_*)=r\mid\mathrm{Bin}(d,z_*)\le r)`$.

At equal quotas the probability of saturation conditional on a zero in a specified column is the actual saturation probability multiplied by $`(d-r)/(d(1-K/n))`$. This uses exchangeability of columns and the fact that a saturated row has exactly $`d-r`$ zeros. The normalized extension ratio in the column is one minus this probability. Indeed each target has exactly $`K+1`$ deletion preimages, so the ratio equals expected available rows divided by $`n-K`$.

All normalized coordinate extension ratios are nonincreasing when any quota increases. Thus a uniform lower bound on this ratio at the balanced vector $`K\mathbf1`$ bounds every extension ratio in each earlier diagonal step. If $`W=(d-r)q_r(\zeta)/(d(1-K/n))`$ for some $`\zeta\ge z_*`$ with $`W<1`$, then every adjacent log decrement of $`p_k`$ through quota $`K`$ belongs to $`[0,L]`$, where $`L=-d\log(1-W)`$.

A sufficient scalar check needing no solution for $`z_*`$ is as follows. Let $`K=k+2`$, $`\zeta=(K+1)/n<1`$, and assume $`n/4\le d\le n/2`$. Define $`\chi=(4d+1)W`$ using $`\zeta`$ in $`W`$. If $`\chi\le1`$, then the truncated mean at $`\zeta`$ exceeds $`dK/n`$. In fact the exact mean is $`d\zeta-\zeta(d-r)q_r(\zeta)`$, from the binomial ratio or differentiation of its truncation sum. The loss is at most $`\zeta d(1-K/n)/(4d+1)<1/4\le d/n`$. Hence $`z_*<\zeta`$, and $`q_r`$ increases in the odds since its log derivative is $`r`$ minus the truncated mean. Also $`L\le dW/(1-W)\le1/4`$. The scalar check is monotone in $`k`$, since both $`q_r(\zeta)`$ and $`(1-K/n)^{-1}`$ increase. A saturated $`K`$ with $`dK/n=r`$ cannot pass this check, as the loss would otherwise force a truncated mean above its cap.

## Geometric sign at logarithmic decrement at most one quarter

Assume $`n\ge10^6`$, $`n/4\le d\le n/2`$, $`k/n\in[1/8,7/8]`$ and $`k-2,k+2`$ are feasible. Define $`\ell_j=\log p_{k+j}`$ and $`D_j=\ell_{j-1}-\ell_j`$ on the feasible support. The normalized orientation inequality makes $`D_j`$ nonnegative and nondecreasing. Let $`b_j`$ denote the terms of the unrestricted polynomial $`\sum_i\binom n i^d q^i`$, normalized by the central term, at its index-$`k`$ geometric circle. In particular $`b_1=b_{-1}<1`$. At the capped geometric radius the corresponding positive magnitude is $`b_j e^{f_j}`$, where

$$
f_j=\ell_j-\ell_0+j(D_0+D_1)/2.
$$

Set $`u=e^{-(D_1-D_0)/2}\in(0,1]`$. The first neighbors contribute $`-2b_1u`$. From $`f_2=D_0-D_2`$ and $`f_{-2}=D_{-1}-D_1`$ and $`0\le D_j\le L`$ through index two, $`f_2+f_{-2}\ge -L-(D_1-D_0)`$. The sum of the even-distance-two magnitudes is therefore at least $`2\sqrt{b_2b_{-2}}e^{-L/2}u`$. By monotonicity of $`D_j`$, $`f_3,f_{-3}\le3\log u`$ when the corresponding terms exist. An absent odd term helps. On each side, the remaining signed terms beginning at distance four sum to a nonnegative contribution, by termwise pairing and log-concavity. Thus the normalized signed value is at least

$$
1-\bigl(2b_1-2\sqrt{b_2b_{-2}}e^{-L/2}\bigr)u
 -(b_3+b_{-3})u^3.
$$

Log-concavity of the unrestricted terms gives $`\sqrt{b_2b_{-2}}\le b_1^2<b_1`$. The bound decreases in $`u`$, so $`u=1`$ gives a valid lower bound.

For the stated sizes let $`x=k/n`$ and $`a=d/(2n x(1-x))\ge1/2`$. Direct Taylor bounds for curvature give $`|\log b_j+a j^2|<.001`$ for $`|j|\le3`$. Indeed each comparison for $`w=k`$ or $`w=n-k`$ at displacement $`|i|\le2`$ costs

$$
\left|\log\left(1+\frac1{w+i}\right)-\frac1w\right|
\le \frac1{2(w-2)^2}+\frac2{w(w-2)}<\frac{162}{n^2}.
$$

Combine the two comparisons, multiply by $`d\le n/2`$, then reconstruct the $`j`$th centered log term from the curvature with weights totaling $`j^2/2\le9/2`$. The error is less than $`729/n`$. The ideal signed lower function with $`L=1/4`$ is $`1-2e^{-a}+2e^{-4a-1/8}-2e^{-9a}`$. Its derivative is positive for $`a\ge1/2`$ since $`e^{3a}>4`$. At $`a=1/2`$ it exceeds $`.0032`$ using $`e^{-1/2}<.6066`$, $`e^{-17/8}>.1194`$, and $`e^{-9/2}<.0112`$. The comparison errors total less than $`1.51/999<.00152`$, since the six unsigned ideal weights have sum below $`1.51`$ and $`e^{.001}-1<1/999`$. The displayed elementary exponential bounds follow from alternating Taylor sums through order 40 or 41. This proves strict positivity. The untailored lower cubic in the actual $`b_j`$ above also gives an exact sufficient test at smaller $`n`$ when its two even neighbors exist.

For the stated sizes the orientation curvature satisfies $`\log G_k>4d/(n+2)\ge n/(n+2)>\log(9/4)`$. The sharp geometric-circle sign theorem therefore gives exactly $`k`$ roots strictly inside, with no boundary root. Consecutive certified indices have ordered radii, and their alternating signs isolate simple negative roots. [Geometric-circle sign theorem](https://github.com/ProgramComputer/open-math-research/tree/8c799d583509ae03f3e3caabc0e3d02449695f15/topics/balanced-arrays/root-distributions/single-sign)

## Exact million-row check and scope

At $`(n,d,r)=(10^6,250000,127000)`$, evaluation uses $`\zeta=(k+3)/n`$. I independently scaled weights by $`2^{100}`$ relative to the mode and rounded each binomial ratio outward. To bound the conditional cap atom, divide its lower and upper weight bounds by the upper and lower sums of weights over $`0\le j\le r`$. A downward tail can be stopped when its outward upper weight is at most $`4096`$ in the scaled units, allowing at most $`d`$ further terms of that weight. The upper enclosure for $`\chi`$ at quota $`504158`$ was

$$
\frac{409304302003975611658533700947125325}
{410259711663590744051197907696277842}<1 .
$$

The lower enclosure at quota $`504159`$ was

$$
\frac{5259252915834156701072274901600329440}
{5251319934040608120787555595422170421}>1 .
$$

Monotonicity of $`\chi`$ supplies every intervening central quota through $`504158`$. The earlier lower edge criterion supplies the remaining smaller quotas. The previously certified 95 outer roots are disjoint by disk counts at indices $`504158`$ and $`507905`$. In total $`504253`$ of the $`508000`$ roots are isolated as simple and negative, and $`3747`$ remain in the intervening annulus. [Earlier lower-edge and outer certificates](https://github.com/ProgramComputer/open-math-research/tree/85dff2a52b0aa34bd50b88b5e18a0601fe15c7ed/topics/balanced-arrays/dense-regime/below-cap/finite-aspect)

The multiplicative comparison is useful well beyond expected overflow $`\log n`$. At fixed positive aspect and an interior density, choose the standardized cap headroom to have square $`\log d+B+o(1)`$ for a large fixed $`B`$. Stirling's formula gives $`d\Pr(\mathrm{Bin}=r)`$ tending to $`e^{-B/2}/\sqrt{2\pi x(1-x)}`$, while truncation changes the normalization by $`o(1)`$. The tail is of order the cap atom times $`\sqrt{d/\log d}`$ from the successive binomial ratios, so the expected number of raw overflow rows is of order $`\sqrt{n/\log n}`$. A shift of one quota does not change these asymptotics. The proof gives no control across the full cap transition, where the absolute log decrement can be large even if its variation with the quota is small.

## Final manuscript and singleton certificate audit

I checked [the manuscript](paper.tex) at SHA-256 `0912184565c5622395c6cdd39e447fd8d4dd9840426edac6656e998360d97da9` against the labeled-array definition. The residual row removed in the ratio $`F_j/F_{j-1}`$ leaves $`N-1`$ rows with a low column at $`K-1`$; the raw one-column ratio is the inverse of $`(N-K)/K`$. Its loss is between those at the balanced residual bases $`K-1`$ and $`K`$. The five lower iterations start at height $`n-5`$ with zero as lower bound and use $`p=(k-j)/(n-j)`$ from depth four back to zero. All balanced residual bases and single extensions used in the certificate have slack above $`d`$. The minimum initial lower quota for the four relevant decrements is $`k-2`$, and their last upper quota is $`k+2`$, so the width uses exactly $`e(n,k-2)`$ and $`e(n,k+2)`$. The cap and feasibility conventions agree with Alexandersson's original labeled arrays.

The curvature-to-log-weight reconstruction uses weights totaling $`j^2/2`$. Two errors below $`162/n^2`$, multiplication by $`d\le n/2`$ and $`j^2/2\le9/2`$ give the stated $`729/n`$. The strict orientation bound supplies $`G_i>9/4`$ at every internal index of the million-row polynomial, so the negative-axis signs give exact open and closed disk counts. For $`0<k<n/8`$ the simpler bound $`\log G_k>d/(k+1)+d/(n-k+1)\ge9/4>\log9`$ suffices for monomial comparison. The high-headroom recursion in the manuscript matches the separately reviewed argument.

For the last 51 singleton quotas, the width used before setting $`u=1`$ is at most $`d\log((1-l)/(1-h))`$. Thus the even coefficient in the exact lower bound is $`2\sqrt{b_{-2}b_2}[(1-h)/(1-l)]^{d/2}`$ and the odd subtractions are $`2b_1,b_{-3},b_3`$. Since $`d=250000`$ is even, the powers are rational, including $`b_{\pm j}=[(\binom n{k\pm j}/\binom n k)^2(v_k^0)^{\pm 2/d}]^{d/2}`$. I independently replayed all 321 blocks in [the quota ledger](quota-blocks.json) using outward binomial weights from their modes at scale $`2^{110}`$ and independent interval powering at scale $`10^{42}`$. The 270 width surpluses and all 51 exact sign lower bounds were strictly positive. The weakest singleton was $`k=505661`$ with certified lower bound

$$
\frac{796514093733798986379260388727927459}
{40000000000000000000000000000000000000000}>0.
$$

The checked [packaged verifier](verify.py) and ledger had SHA-256 `26fcc19c3425904551bfd5d9467edfeebfcc39ad4136bd77c8702fc0bbc53f64` and `92af20928b4d471671dcaaabc01045d5f9b625d24b28f8530a3647a7310ac885`. The first 505,661 roots and the previously certified 95 outer roots occupy disjoint bands, giving 505,756 simple negative roots and 2,244 remaining roots counted with multiplicity. The argument is an exact partial root count for this instance. It does not classify the transition annulus or settle the original real-rootedness conjecture.
