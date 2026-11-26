# Centering the recursion at the truncation with the same mean

This proof specifies the inequalities implemented by the [exact checker](centered.py). Take the fixed $`n,d,r`$ of the [instance](README.md). All intervals below use outward rational rounding.

## The reference extension loss

For a column density $`p`$, let $`z(p)`$ give mean $`dp`$ to $`J\sim\mathrm{Bin}(d,z)`$ conditional on $`J\le r`$. Put $`L^*(p)=\log(z/(1-z))-\log(p/(1-p))`$. Conditioning one bit to be absent in this reference model leaves $`d-1`$ Bernoulli variables conditioned on the same cap. Its top probability is $`q^*(p)=1-e^{-L^*(p)}`$, by the binomial mean identity in the [marked-row lemma](../paper.pdf). Write $`v=p(1-p)`$ and $`B=(z-p)(r-(d-1)p)`$. Differentiating that identity in the log odds gives $`V=\mathrm{Var}(J)=d(v-B)`$, and

$$
(L^*)'(p)=d/V-1/v=B/[v(v-B)] .
$$

Indeed $`V=dp(1-z)-d(z-p)(r-dp)`$. The identity $`dp=dz-z(d-r)\Pr(J=r)`$ gives $`V\le dz(1-z)`$ by differentiation since the top mass increases in log odds. Hence $`z-p`$ is nondecreasing. On a tested interval $`p_0\le p\le p_1`$ above $`1/2`$, the program bounds $`B`$ by combining the endpoint bounds of its two positive factors, and bounds $`v`$ by its endpoint values. Its checks require $`0<B\le B_{\max}<\min v`$. This gives a uniform upper derivative bound $`M`$ and a lower derivative when needed.

## Error recursion for arbitrary residual margins

For a residual height $`N`$ and margins $`q_h`$, put $`p=\sum_hq_h/(Nd)`$ and $`L_i=-\log(1-e_i)`$, where $`e_i`$ is the probability of saturation of a marked row conditional on missing column $`i`$. At depth $`j`$ we bound $`|L_i-L^*(p)|`$ for every possible residual vector and every marked column. The initial diagonal paths have coordinate spread at most one, so the spread at depth $`j`$ is at most $`j+1`$. The rectangular interval $`[p_0,p_1]`$ in the code contains all individual column densities and all mean densities through the terminal depth. The feasibility checks allow every mask used in the comparison.

At terminal depth, orientation bounds the actual loss below by the previously proved eight-step balanced lower bound at the smallest possible balanced quota and above by $`q^*(p_1)`$. The same interval contains the reference loss for the actual mean density: the balanced lower bound is below its matched-mean reference at the minimum realizable density, and $`q^*`$ is increasing. The log error is thus at most the loss interval width divided by $`1-q^*(p_1)`$. Denote the next-depth log-error bound by $`E`$.

Given a specified missing column $`i`$, let $`f(S)`$ be the number of completions when the marked row occupies exactly $`S\subseteq[d]\setminus\{i\}`$. Put $`w_h=q_h/(N-q_h)`$ and $`w(p)=p/(1-p)`$. For $`h\notin S\cup\{i\}`$ with $`|S|=j_0<r`$ the exact ratio $`f(S\cup\{h\})/f(S)`$ is $`w_h\exp L_{\mathrm{res},h}`$, with residual margin vector $`\boldsymbol q-\mathbf1_{S\cup\{h\}}`$ at height $`N-1`$. Its mean density equals

$$
p'=p+(dp-j_0-1)/[d(N-1)] .
$$

Within a fixed $`j_0`$-element layer, compare supports differing by swapping $`h`$ for $`g`$. Both residual insertion ratios for the comparison use the same base, obtained by lowering the columns in the union of the two supports. The reference losses at that common base cancel. The ratio of the two mask weights, in either direction, is at most $`K=(w_{\max}/w_{\min})e^{2E}`$. Matching supports that contain just one of $`h,g`$ shows that the vacancy probabilities $`v_h,v_g`$ on the layer have ratio at most $`K`$ in either direction: the common event that both are vacant contributes equally. The mean vacancy probability over the $`d-1`$ available columns is $`(d-1-j_0)/(d-1)`$. Thus the vacancy-weighted average odds of an unmarked column differ from the unweighted average by at most $`(K-1)(w_{\max}-w_{\min})`$. This follows by subtracting the smallest odds from each term, since the weights sum to one.

At depth $`j`$ let $`b_0=(j+1)/N`$ bound the spread of densities. Then $`W=b_0/(1-p_1)^2`$ bounds the spread of their odds. Omitting $`i`$ costs at most $`W/(d-1)`$ in the unweighted average. The average of all column odds differs from $`w(p)`$ by at most $`b_0^2/(1-p_1)^3`$, by Taylor's theorem and cancellation of the linear term. The resulting error in log average odds is bounded by

$$
\epsilon=A/(w(p_0)-A),\qquad A=(K-1)W+W/(d-1)+b_0^2/(1-p_1)^3 .
$$

The checker verifies $`A<w(p_0)`$ and uses $`K\le(1+W/w(p_0))/(1-2E)`$.

If $`U_{j_0}=\sum_{|S|=j_0}f(S)`$, the ratio $`(j_0+1)U_{j_0+1}/[(d-1-j_0)U_{j_0}]`$ is the layer average of the insertion odds over unmarked columns. By the induction bound at $`p'`$ and the derivative bound $`M`$, the difference between its logarithm and the reference log odds $`\log w(p)+L^*(p)`$ has magnitude at most

$$
E+\epsilon+M |dp-j_0-1|/[d(N-1)] .
$$

For deficit $`x=r-j_0`$ sum these errors over the $`x`$ steps back from the cap. The error in the log weight relative to the top atom, compared with the reference $`\mathrm{Bin}(d-1,z(p))`$ truncated at $`r`$, is at most $`ax+bx^2`$, where $`b=M/[d(N-1)]`$ and $`a=E+\epsilon+b(r-dp_0+1)`$.

Let $`X`$ be the deficit under this reference with parameter $`z(p_0)`$, let $`m=a\mathbb EX+b\mathbb EX^2`$ and let $`G=\mathbb E\exp(aX+bX^2)`$. Deficits at the lower parameter stochastically dominate those at any actual parameter, since the binomial odds give monotone likelihood ratios. Summing the top-normalized weights shows that the ratio of the actual to the reference top mass lies between $`1/G`$ and $`e^m`$: for the upper bound use Jensen's inequality on $`e^{-ax-bx^2}`$. With $`Q=q^*(p_1)`$, passing from probabilities to negative log survivals gives the new error bound

$$
\max\left\lbrace \frac{Qm}{1-m-Q},\ \frac{Q(1-1/G)}{1-Q}\right\rbrace  .
$$

For the first term use $`e^m\le1/(1-m)`$ and bound the log difference by the mass difference divided by the smaller survival probability. For the second term the smaller survival probability is at least $`1-Q`$. The positive denominators are checked at each depth.

The program evaluates the moments by summing the positive binomial weights down from the cap with two directed integer bounds. For the exponential moment each successive step multiplies by at most $`1/[1-a-b(2x+1)]`$, using upward-rounded $`a,b`$. When ending the summation early it bounds all remaining ratios by the current binomial ratio times the largest exponential step factor on the support. The geometric series gives the discarded upper mass, and $`r`$ and $`r^2`$ bound the missing moment factors. Matched tilts are enclosed by independently checking both endpoints of a dyadic bisection.

## From log losses to root counts

At phase $`\ell`$ from quota $`k`$ to $`k+1`$ the mean density is $`(k+\ell/d)/n`$. The total log decrement of the normalized cap probability differs by at most $`dE_0`$ from the sum of $`L^*`$ at these $`d`$ points, where $`E_0`$ is the final error. In two neighboring paths the corresponding phases differ in density by exactly $`1/n`$. The log curvature of the raw coefficient is therefore within $`2dE_0`$ of the sum of the known binomial log curvature and $`d/n`$ times an average of $`(L^*)'`$ over those phase intervals.

The checker first tests whether the resulting log-curvature lower bound exceeds $`\log4`$. Otherwise it encloses all five curvatures from $`k-2`$ through $`k+2`$ in $`[a_0,b_1]`$. At geometric radius $`v_k=\sqrt{a_{k-1}/a_{k+1}}`$, the normalized magnitude at offset $`j`$ is between $`e^{-b_1j^2/2}`$ and $`e^{-a_0j^2/2}`$ for $`|j|\le3`$. This follows by summing second differences with weights of total $`j^2/2`$. The lower sign test is

$$
1-2e^{-a_0/2}+2e^{-2b_1}-2e^{-9a_0/2}>0 .
$$

All further alternating pairs from distance four contribute nonnegatively. The globally valid $`9/4`$ second-quotient bound converts the strict sign into exactly $`k`$ zeros in the open and closed disks. The enlarged phase interval in each block includes the full stencil. The replay certifies 794 indices by factor four and 36 by the seven-term test, covering all 830 integers from 506471 to 507300. [Full output](centered-output.txt) · [Geometric disk theorem](../../../../../root-distributions/single-sign/README.md)
