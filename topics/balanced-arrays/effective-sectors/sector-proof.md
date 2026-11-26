# Effective rank and dimension bounds for balanced arrays

Let $`a_k`$ count the labeled $`n`$ by $`d`$ binary arrays whose row sums are at most $`r`$ and whose column sums are all $`k`$. Write $`D=\lfloor nr/d\rfloor`$, $`p_k=a_k/\binom nk^d`$ and $`g_k=((1+1/k)(1+1/(n-k)))^d`$. We use the previously proved orientation inequality $`p_k^2\ge p_{k-1}p_{k+1}`$. The $`a_k`$ are positive throughout their support, as one sees by placing consecutive cyclic blocks of $`k`$ ones in the successive columns. The maximum row sum then equals $`\lceil dk/n\rceil`$. [Orientation proof](https://github.com/ProgramComputer/open-math-research/blob/research/topics/balanced-arrays/orientation-normalization.md)

**Numerical sector theorem.** If $`n\ge1024`$, $`d\ge n/4`$ and $`10r\ge9d`$, the polynomial has $`D`$ simple negative roots.

**Effective sector theorem.** Let $`1/2<\rho<1`$ and $`c>\rho(1-\rho)\log4`$ be rational. There is an effectively computable $`N(c,\rho)`$ such that the same conclusion holds whenever $`n\ge N(c,\rho)`$, $`d\ge cn`$ and $`r\ge\rho d`$. The numerical theorem below uses much smaller constants than the general construction.

The existing all-cap eventual theorem gives an unspecified threshold even with no rank or dimension restrictions. Here the cutoff can be calculated using elementary operations with rigorous error bounds. The issue outside these sectors is how to handle quotas close to the cap where the binomial approximation and factor-four separation can both fail.

## Alternating signs at geometric nodes

Write $`G_i=a_i^2/(a_{i-1}a_{i+1})\ge g_i>1`$. For $`1\le k<D`$ take $`x_k=\sqrt{a_{k-1}/a_{k+1}}`$. Successive nodes increase because the ratios $`a_{i-1}/a_i`$ increase. Put $`w_j=a_{k+j}x_k^j/a_k`$ for indices in the support. Then $`w_0=1`$, $`w_{\pm1}=t=1/\sqrt{G_k}`$, and the weights decrease outwards on both sides. The sign of interest is $`\sum_j(-1)^j w_j`$. At a quota with $`g_k>4`$, it is at least $`1-2t>0`$ by pairing every second term with the following term on each side. If both sides reach distance three, the same pairing gives the stronger lower bound

$$
1-2t+t^2\sum_{e\in\lbrace-1,1\rbrace}\frac1{G_{k+e}}\left(1-\frac{t}{G_{k+e}G_{k+2e}}\right).
$$

Indeed, $`w_{2e}=t^2/G_{k+e}`$ and $`w_{3e}/w_{2e}=t/(G_{k+e}G_{k+2e})`$. Positive signs at all these nodes, together with the constant and the leading term, yield one root in each of $`D`$ disjoint negative intervals.

## Explicit constants

Assume $`n\ge1024`$. For every $`i`$ the bounds $`\log(1+1/i)\ge1/(i+1)`$ and convexity give $`\log g_i\ge4d/(n+2)\ge n/(n+2)`$, so $`g_i>27/10`$. We may take $`d<n`$ since otherwise all $`g_i>4`$. Write $`g=g_k`$ and consider a quota with $`g\le4`$. Then $`23n/100<k<77n/100`$. Indeed, outside that interval convexity and symmetry give

$$
\log g\ge \frac14\left(\frac1{23/100+1/n}+\frac1{77/100+1/n}\right)>1.39>\log4.
$$

Every quota at distance at most three from $`k`$ is present. For $`|i-k|\le2`$ we have $`i/n\le193/250`$. Select the $`d`$ uniform $`i`$-subsets independently, one per column. Each row sum is binomial with parameters $`d,i/n`$. Union bounding over rows, increasing the success probability to $`b=193/250`$, and applying the exponential Markov bound at $`a=9/10`$ gives

$$
1-p_i\le n\exp[-d H(a,b)], \qquad
H(a,b)=a\log(a/b)+(1-a)\log((1-a)/(1-b)).
$$

This tail bound follows by minimizing $`((1-b)+b e^s)^d e^{-sda}`$ over positive $`s`$. For $`a\ge b>1/2`$, the second derivative of $`H`$ in $`a`$ is $`1/(a(1-a))\ge1/(b(1-b))`$, so $`H(a,b)\ge(a-b)^2/(2b(1-b))`$. Thus $`p_i\ge99/100`$ for every $`n\ge1024`$: $`n e^{-nH/4}`$ decreases on this range and already lies below $`1/100`$ at its left endpoint.

For $`|i-k|\le1`$ the derivative of $`d\log[(1+1/y)(1+1/(n-y))]`$ on the segment between $`i,k`$ has absolute value at most $`2n/(.228n)^2<.038`$ since $`d<n`$. Hence $`g_i\le1.04g`$ and $`G_{k\pm1}\le1.04g/(.99)^2<1.07g`$. The inequality $`t<.61`$ and the global lower bound $`G_j>2.7`$ turn the signed sum above into a quantity at least $`1-2t+1.70t^2/g`$. This quadratic decreases for $`0\le t\le1/\sqrt g`$ because $`1.70t/g<1`$. Its value there is at least

$$
1-2/\sqrt g+1.70/g^2>0.
$$

The last expression increases for $`g\ge2.7`$ since $`g^{3/2}>3.40`$, and is positive at $`2.7`$. This proves the numerical theorem. The comparison script uses rational bounds for the few exponential constants.

## General effective cutoff

Choose rational $`1/2<\beta<\rho`$ with $`c>\beta(1-\beta)\log4`$, and set $`h=1-\beta`$. Take $`d<n`$ as above. For $`n`$ large enough that $`c((\beta+1/n)^{-1}+(h+1/n)^{-1})>\log4`$, every quota with $`g_k\le4`$ lies in $`hn<k<\beta n`$. All larger $`n`$ satisfy the same bound. Also $`g_i\ge\exp(4cn/(n+2))\ge e^{2c}`$ for $`n\ge2`$.

Put $`q=g_k^{-1/2}`$ and fix a rational $`e^{-c}<Q<1`$. The bilateral series $`\Theta(q)=\sum_{j\in\mathbb Z}(-1)^j q^{j^2}`$ is bounded below by $`\exp(-3Q/(1-Q)^2)`$ for $`0<q\le Q`$. Indeed its product is $`\prod_{m\ge1}(1-q^{2m})(1-q^{2m-1})^2`$ and $`-\log(1-x)\le x/(1-Q)`$ for $`x\le Q`$. [Jacobi triple product, DLMF 20.5.9](https://dlmf.nist.gov/20.5.E9)

Choose a positive rational $`\eta`$ below that lower bound, and an odd positive $`J`$ such that $`2Q^{(J+1)^2}/(1-Q)<\eta/3`$. Choose rational $`\epsilon>0`$ with $`(2J+1)(\exp(J^2\epsilon/2)-1)<\eta/3`$. Let $`\delta=(\rho-\beta)/2`$, $`\lambda=2c\delta^2`$. Impose $`n\ge 2(J+1)/h`$, $`n\ge(J+1)/\delta`$, and $`n\ge1/\lambda`$. The full window through $`k\pm(J+1)`$ is then in the support and its quota densities are at most $`\rho-\delta`$. On this window $`1-p_i\le E(n)=n\exp(-\lambda n)`$ by the binomial bound above or its limit at zero, using $`H(a,b)\ge 2(a-b)^2`$ from $`\partial^2 H/\partial a^2\ge4`$.

Increase $`n`$ until $`E(n)<1`$ and

$$
\frac{8J}{h^2 n}-2\log(1-E(n))<\epsilon.
$$

Such an integer is found by doubling, and the inequality holds thereafter by monotonicity. For $`|i-k|\le J`$ the derivative bound from the numerical proof gives $`|\log g_i-\log g_k|\le8J/(h^2 n)`$. The three probabilities in $`G_i/g_i`$ give $`|\log G_i-\log g_i|\le-2\log(1-E(n))`$. Thus $`|\log G_i-\log g_k|<\epsilon`$.

Since $`w_{\pm1}=G_k^{-1/2}`$ and the successive log slopes on each side change by $`-\log G_{k\pm j}`$, it follows that $`|\log w_j+j^2\log g_k/2|\le j^2\epsilon/2`$ for $`|j|\le J`$. The sum of absolute errors between $`w_j`$ and $`q^{j^2}`$ on this window is at most $`(2J+1)(e^{J^2\epsilon/2}-1)`$. The omitted ideal tail has absolute value at most $`2Q^{(J+1)^2}/(1-Q)`$. Therefore the signed sum through distance $`J`$ is positive. The omitted actual tails each begin with an even index, and pairing successive terms gives a nonnegative remainder on each side. This completes the proof and specifies a terminating threshold calculation using strict comparisons.
