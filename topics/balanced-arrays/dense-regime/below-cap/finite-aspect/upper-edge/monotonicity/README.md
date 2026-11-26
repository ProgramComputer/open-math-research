# Slack-error monotonicity at fixed near-balanced phase

Research note, November 26, 2026. Let $`M`$ be the number of positive row deficits in a uniform balanced-array fiber. Fix height $`n`$, dimension $`d`$, cap $`r<d`$, and phase $`\ell`$. At the fiber with $`\ell`$ columns of size $`k+1`$ and the rest of size $`k`$, put $`s=nr-dk-\ell`$ and

$$
E(s)=\mathbb EM-\frac{ns}{n+s-1},\qquad R=r(1-r/d).
$$

When $`s=0`$ take $`E(s)=0`$. The proposed monotonicity is $`E(s+d)\ge E(s)`$, with $`\ell`$ fixed. I normalize a comparison by the larger slack, $`(s+d)/(n\sqrt R)`$. This convention tests that both fibers are within the proposed scale. At fixed phase, global monotonicity fails. The counterexamples below still leave the full range $`(s+d)/n\le\sqrt R`$ undecided.

## Exact finite obstruction

There is a finite example at $`(n,d,r,\ell)=(8600,80,2,0)`$, from $`k=15`$ to $`k=16`$. The larger slack is $`16000`$ and the larger squared scale is $`128000/72111<16/9`$. At $`k=15`$ the value $`10^6 E/n`$ lies strictly between $`341042`$ and $`341043`$. At $`k=16`$ it lies strictly between $`341077`$ and $`341078`$. Both quotas are positive and nonsaturated.

For this larger example, the independent rank-two checker labels the $`L`$ occupied column stubs. A row of size two matches two stubs from different columns. If there are $`h`$ such rows, the matchings have size $`h`$ in the complete multipartite graph whose part sizes are the column quotas. A matching, with its remaining singletons, has $`(n)_{L-h}`$ injections into the labeled rows. Dividing by the product of column factorials is common to all $`h`$ and cancels from $`\mathbb EM`$. For each column compute the polynomial counting all matchings of its own forbidden within-column edges. The product gives the numbers $`q_i`$ of size-$`i`$ matchings of forbidden edges. Inclusion–exclusion gives the allowed matching number

$$
m_h=\sum_{i=0}^h(-1)^i q_i
\frac{(L-2i)!}{2^{h-i}(h-i)!(L-2h)!}.
$$

The expectation of $`M=n-h`$ with weights $`m_h(n)_{L-h}`$ gives the two exact fractions. A separate column-by-column dynamic program computes the same rational expectations directly in the full $`8600`$-row example. After $`j`$ columns, recording the number $`h`$ of double rows fixes the numbers of single and empty rows at $`A=jk-2h`$ and $`B=n-jk+h`$. Choosing $`i`$ single rows and $`k-i`$ empty rows for the next labeled column leads to $`h+i`$ double rows with multiplicity $`\binom Ai\binom B{k-i}`$. At the final column the number of active rows is $`n-h`$. The two resulting fractions agree exactly with the matching counts.

## The scalar limit gives rigorous labeled-array obstructions

Fix $`d,r`$ and odds $`w>0`$. Let $`S`$ have weights $`\binom djw^j`$ for $`0\le j\le r`$, normalized by their sum. Write $`t=r-\mathbb ES`$ and $`p_r=\Pr(S=r)`$. At equal quotas $`k_n`$ with $`\left|k_n-n\mathbb ES/d\right|\le1`$,

$$
\frac{E(nr-dk_n)}n\longrightarrow g(t)=\frac1{1+t}-p_r.
$$

To verify it, generate independent rows, assigning each allowed particular subset probability proportional to $`w^{|I|}`$. Conditioning on the exact equal column sums gives the uniform original array law, since every allowed array with those sums has the same weight. The conditioning event has at least inverse-polynomial probability at fixed $`d,r,w`$. Choose a single joint row-type histogram by flooring the expected counts of all subsets of size at least two. Solve the $`d`$ column equations by adjusting the counts of the $`d`$ singleton types, then solve the total number of rows by the count of the empty type. Each correction is bounded as $`n`$ varies, and all these types have positive probability. All counts are nonnegative for sufficiently large $`n`$. Stirling's formula on this one multinomial type gives probability $`\exp[-O_{d,r,w}(\log n)]`$. Before conditioning $`M/n`$ is exponentially concentrated around $`1-p_r`$ by the Bernoulli concentration bound. The same convergence in probability and mean therefore holds after conditioning. Subtract the limit $`t/(1+t)`$ of the lower model divided by $`n`$.

Consequently two points with $`t_A<t_B`$ and $`g(t_A)>g(t_B)`$ imply a violation at some adjacent pair between the corresponding rounded quotas, at fixed phase zero, for every sufficiently large $`n`$. Otherwise every step from the lower to the higher slack would be nondecreasing. The endpoint convergence gives a contradiction. When $`t_B/\sqrt R`$ is strictly below a proposed scale, all intermediate pairs eventually satisfy that scale as well.

At $`d=80,r=2`$, the Bernoulli parameters $`p_A=1/535`$ and $`p_B=1/555`$ correspond to odds $`w_i=p_i/(1-p_i)`$. The exact scalar values are

$$
t_A=\frac{153258}{82759},\qquad t_B=\frac{54846}{29533},
\qquad
g(t_A)=\frac{6662598651}{19532530903},\qquad
g(t_B)=\frac{2549934857}{7475895021}.
$$

Here $`t_A<t_B`$, $`g(t_A)>g(t_B)`$, and $`t_B^2/R<16/9`$. This proves violations below $`4/3`$ for every sufficiently large height at these fixed rank and dimension, independently of the finite example.

## Central caps give obstructions below $`5/4`$

Let $`d`$ be even and tend to infinity with $`r=d/2`$, so $`R=d/4`$. For a fixed $`\lambda>0`$, set the uncapped binomial parameter to $`p=1/2-\lambda/(2\sqrt d)`$ and condition the size on $`S\le r`$. The uncapped standardized deficit converges to a normal law of mean $`\lambda`$ and variance one. Its conditioning probability tends to $`\Phi(\lambda)>0`$. The first moments of the conditional standardized deficit converge because the uncapped second moments are bounded and the conditioning probability stays away from zero. The limiting conditional mean is $`\alpha(\lambda)=\lambda+h(\lambda)`$, where $`h(\lambda)=\phi(\lambda)/\Phi(\lambda)`$. Stirling's formula at the central binomial atom gives $`\sqrt R\,\Pr(\mathrm{Bin}(d,p)=r)\to\phi(\lambda)`$, since the factor from $`p(1-p)`$ after removing $`1/4`$ is $`(1-\lambda^2/d)^{d/2}`$. Thus at the conditioned mean deficit $`t`$,

$$
\frac t{\sqrt R}\longrightarrow \alpha(\lambda),\qquad
\sqrt R\thinspace{}g(t)\longrightarrow \frac1{\alpha(\lambda)}-h(\lambda).
$$

For $`\lambda_A=23/25`$ and $`\lambda_B=93/100`$, the exact rational normal enclosures in the checker give $`\alpha_A<\alpha_B<5/4`$ and a strictly larger limiting error at $`A`$, by a gap above $`18\cdot10^{-6}`$. The checker uses

$$
h(\lambda)=
\frac{e^{-\lambda^2/2}}
{\sqrt{\pi/2}+\int_0^\lambda e^{-u^2/2}\thinspace{}\mathrm du}.
$$

The numerator and the integral are bounded by alternating Taylor sums. A rational bracket for $`\sqrt{\pi/2}`$ follows by squaring and using the alternating arctangent series in Machin's formula for $`\pi`$. Therefore for each sufficiently large even $`d`$ the finite scalar odds produce a strict decreasing interval below $`5/4`$. The fixed-$`d`$ transfer above proves an adjacent labeled-array obstruction at that scale for every sufficiently large height, with the height threshold allowed to depend on $`d`$. This is an existence result and gives no explicit height threshold.

## Scope and reproduction

This obstruction limits a proposed strengthening of the [row-deficit switching theorem](../README.md). The scale-one comparison, with both quotas at normalized slack at most one, remains open. The examples concern a row-occupancy statistic. Real-rootedness of the underlying array polynomials remains a separate question. **Formal verification**　⬜ None. The finite witness was reconstructed independently using two exact enumerations. The separate limiting argument and its constants are included for research review.

~~~sh
python3 -IB verify.py
python3 -IB limits.py
~~~

[Original balanced-array conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/2)
