# Reduction to quotas with two large variances

Assume $`u=\log n\ge10^6`$, $`n^{.99}\le d\le n`$, and put $`s=d/n`$. For an internal quota $`k`$ let $`b_k=\log(a_k^2/(a_{k-1}a_{k+1}))`$ and $`t_k=\sqrt{a_{k-1}/a_{k+1}}`$. The published effective comparison extends to this strip at each pair of feasible densities in $`[s/3,1-s/3]`$. As a consequence, a wrong or zero geometric sign requires

$$
b_k<100/u,\qquad
\frac{n x(1-x)}d>u/200,\qquad
\frac{n\thinspace{}\mathrm{Var}(S_k)}{d^2}> u/110,
$$

where $`x=k/n`$ and $`S_k`$ has tilted capped-binomial weights with mean $`dx`$. These are necessary conditions for failure of the geometric witness. An angular witness is required only in the regime where both normalized variances grow at least logarithmically. This assertion does not prescribe the order of a mixed family of angular and geometric witnesses.

For the extension, put $`T=100/\min(s,1/4)\le400 n^{.01}`$. The explicit Bessel and row-atom bound in the published proof is derived for regular profiles if $`n^{-1/4}\le\min(s,1/4)/12`$, $`n/(2T^2)\ge10`$, $`A-n/d\ge n/(2T)`$, and $`\log(2\pi n)\le n/(4T^2)`$. These follow from $`u\ge10^6`$ and the displayed $`T`$ bound. In its last expression the aligned exponent $`n^{1/5}/(40T^2)`$ is at least $`n^{.18}/(40\cdot400^2)`$, which exceeds $`1000(T^2+u)`$; this follows at the lower endpoint and increases thereafter by comparing logarithms. Thus the tail is still below $`n^{-10}`$ in the subset normalization. The main chart comparison uses only $`d\ge n^{.99}`$, $`\lambda\ge d/5`$ and $`u\ge10^6`$. The determinant-change term $`25\eta^2/s`$ with $`\eta=n^{-1/4}`$ is at most $`25n^{-.49}`$. The previous regular second moment is bounded by $`100(nd+1)e^{20/s}`$, now possibly superpolynomial. In the cross-event Cauchy–Schwarz bound its logarithm contains $`10/s\le10n^{.01}`$, whereas the negative tail exponent is at least $`d\eta^2\ge n^{.49}`$. The self-bad array tails also remain negligible. This yields the original $`n^{-1/8}`$ slope comparison in the stated strip.

Suppose now $`b_k\le\log4`$; larger curvature already gives the correct sign. Then $`\min(k,n-k)\ge d/\log4-1`$ by binomial normalization. The two immediate slopes exist even at a saturated neighbor. As in the published proof the scalar deficit curvature is less than two, since the baseline log curvature costs at most $`10/(ns^2)`$, and therefore $`h=nr/d-k>\sqrt n/2`$. In the latter inequality $`1/s\le n^{.01}\ll\sqrt n`$ suffices. All quotas at distance $`J+2`$ with $`J\le u+2`$ exist and have density in $`[s/3,1-s/3]`$. The tilted variances there are at least $`s^2\sqrt n/32`$ from the carried-load comparison.

If $`b_k\ge100/u`$, choose $`\lambda_\theta=50/u`$, $`J`$ the smallest odd integer at least $`2/\lambda_\theta`$, and $`\epsilon=(\lambda_\theta/4)e^{-\pi^2/(4\lambda_\theta)}`$. Here $`\log(1/\epsilon)\le .06u`$ and $`n^{-1/8}<\epsilon/100`$. The original scalar-curvature argument uses $`s`$, the actual aspect, in its error bounds. The sufficient scalar height inequalities are satisfied because
$`12\log10+\log(J+2)+3\log(1/s)+.06u < u/2`$ and
$`14\log10+\log(1/s)+.06u<u/4`$.
The theta lemma itself needs only $`\lambda_\theta\le b_k/2`$, independent of the global lower bound on all curvatures. Thus the geometric sign is strict and correct. Notice that the earlier sufficient choice $`\lambda_\theta\le2s/(1+2/n)`$ was used only to check this local center inequality automatically.

At a remaining center $`b_k<100/u`$, the two individual orientation terms imply $`k+1,n-k+1>du/100`$. For the displayed $`nv/d`$ bound use the stronger sum
$`1/(k+1)+1/(n-k+1)=(n+2)/[(k+1)(n-k+1)]`$.
Multiplying and rearranging gives $`k(n-k)>du(n+2)/100-(n+1)`$, hence $`nv/d>u/200`$.

For the scalar bound put $`\mu_k=dk/n`$ and $`V(\mu)=\mathrm{Var}(S)`$ at real tilt mean $`\mu`$. The entropy contribution is $`I_k=n\int_{-s}^s (s-|t|)/V(\mu_k+t)\,dt`$. Its difference from $`b_k`$ has absolute value at most
$`2\cdot10^9/\sigma_{\min}+4\cdot10^{11}n^{-1/4}+2n^{-1/8}+10/(ns^2)<1/u`$,
where $`\sigma_{\min}\ge s n^{1/4}/\sqrt{32}\ge n^{.24}/\sqrt{32}`$. This uses the scalar local limit estimate and the standard-deviation Lipschitz bound exactly as before. Some tilt point in this interval therefore has $`\sigma\ge s\sqrt{nu/101}`$. Since $`|d\sigma/d\mu|\le10^9`$, the center obeys $`\sigma(\mu_k)\ge s(\sqrt{nu/101}-10^9)>s\sqrt{nu/110}`$. This is the claimed lower bound.

In particular, all geometric nodes give the required strict signs if $`r\le d^2u/(200n)`$ and $`d\ge n^{.99}`$. Indeed $`k+1\le nr/d+1\le du/200+1`$ forces $`b_k\ge d/(k+1)>100/u`$. The main use of the reduction is the simultaneous lower bounds on the column precision and the row-size variance when testing the angular integral at unrestricted caps.
