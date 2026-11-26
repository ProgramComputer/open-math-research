# A variance comparison for ordered angular test points

Let $`S`$ be the binomial law in $`d`$ trials at arbitrary positive odds, conditioned on $`S\le r`$ with $`1\le r<d`$. Write $`\mu=\mathbb ES`$, $`V=\mathrm{Var}(S)`$, $`q_s=s(d-s)/(d(d-1))`$. Let $`\widetilde V`$ be the variance of the probability mass proportional to $`q_s\Pr(S=s)`$. For $`\mu\le d/2`$ we prove $`\widetilde V\le2V`$. For $`h=d-\mu\le d/2`$ we give

$$
\frac{\widetilde V}{V}\le 1+\frac d{d-1}\frac{d-2h}{d-h}\left(2-\frac1h\right).
$$

The second bound is strictly below three by an amount of order at least $`d^{-1/2}`$ as $`d`$ grows, uniformly in the real tilt. The proof uses a one-sided bound for a discrete Stein kernel.

## A third-moment bound

For any positive log-concave mass $`p_0,\ldots,p_b`$ of total mass one on an integer interval beginning at zero, let $`T`$ have that mass, $`m=\mathbb ET`$, and
$`\tau_j=\sum_{i\le j}(m-i)p_i/p_j`$. Summation by parts gives $`\mathbb E[(T-m)f(T)]=\mathbb E[\tau_T(f(T+1)-f(T))]`$, where $`\tau_b=0`$. The tail expression shows $`\tau_j\ge0`$ since its tail's conditional mean is at least the overall mean. We claim $`\tau_{j+1}-\tau_j\le m`$.

Given $`T>j`$, the excess $`T-j-1`$ is stochastically dominated by $`T`$: the ratio $`p_{i+j+1}/p_i`$ is nonincreasing in $`i`$ by log-concavity, including the zero extension. Its conditional mean is at most $`m`$. Thus the tail expression gives $`\tau_j\le(j+1)\Pr(T>j)/p_j`$. Write $`R=p_{j+1}/p_j`$. If $`R<1`$, the tail ratio is at most $`R/(1-R)`$ by the geometric series. The recurrence $`\tau_{j+1}-\tau_j=(1/R-1)\tau_j+m-j-1`$ proves the claim; for $`R\ge1`$ nonnegativity suffices.

Using $`f(j)=j`$ and $`f(j)=(j-m)^2`$ gives $`\mathbb E\tau_T=\mathrm{Var}(T)`$ and $`\mathbb E(T-m)^3=\mathrm{Var}(T)+2\mathrm{Cov}(\tau_T,T)`$. The one-sided slope bound implies $`\mathrm{Cov}(\tau_T,T)\le m\mathrm{Var}(T)`$ by independent copies. Hence
$`\mathbb E(T-m)^3\le(2m+1)\mathrm{Var}(T)`$. The same identity gives equality for a geometric law on the nonnegative integers, where the sums converge absolutely.

## The low-mean case

For a positive log-concave mass at $`0,\ldots,b`$, variance under conditioning on $`X\le j`$ is nondecreasing in $`j`$. To see it first observe that every nonnegative log-concave random variable $`U`$ on an integer interval beginning at zero satisfies $`\mathrm{Var}(U)\le m(m+1)`$ for $`m=\mathbb E U`$. Indeed the excess given $`U>j`$ is dominated by $`U`$, so $`\mathbb E[U(U-1)]/2=\sum_{j\ge0}\mathbb E[(U-j-1)_+]\le m\sum_{j\ge0}\Pr(U>j)=m^2`$.

Put $`U_{j-1}=j-1-X`$ under the old cap, with mean $`m`$, and let $`p`$ be the conditional probability of the new top atom under cap $`j`$. The reflected deficit $`U_j`$ under the new cap stochastically dominates $`U_{j-1}`$ because the likelihood ratio of their masses is proportional to $`p_{j-i}/p_{j-1-i}`$ at deficit $`i`$ and is nondecreasing; any new support point lies above the old support. Therefore $`(1-p)(m+1)=\mathbb E U_j\ge m`$. Its variance is $`(1-p)\mathrm{Var}(U_{j-1})+p(1-p)(m+1)^2\ge\mathrm{Var}(U_{j-1})`$ by the variance bound. This proves the truncation claim.

Expose the first Bernoulli cell. When it is occupied the remaining binomial has cap $`r-1`$, whereas when it is empty the cap is $`r`$. The preceding variance ordering and conditional variance decomposition give $`\mathrm{Var}(S\mid X_1=1)\le V`$. Given the first cell occupied, the second is empty with probability at least $`1-\mu/d`$. Indeed $`V\le\mu(1-\mu/d)`$ by the capped-binomial variance comparison, equivalently the covariance between distinct cells is nonpositive. For $`\mu\le d/2`$, the event has probability at least one half under this conditioning. Another variance decomposition gives $`\mathrm{Var}(S\mid X_1=1,X_2=0)\le2V`$. This is precisely $`\widetilde V`$ by exchangeability. The argument includes single-atom conditionals.

## The high-mean case

Write $`X=d-S`$ and $`h=\mathbb EX`$; then $`X\ge c=d-r\ge1`$. Apply the third-moment bound to $`X-c`$ to obtain $`\kappa_3(X)\le(2h-1)V`$. Let $`W=X(d-X)`$, $`Z=X-h`$, and $`B=\mathbb EW=h(d-h)-V`$. Under the $`W`$-weighted law, variance is the second moment about $`h`$ less the squared shift of the mean. Hence

$$
\frac{\widetilde V}{V}\le1+\frac{(d-2h)\kappa_3(X)-(\mathbb E Z^4-V^2)}{BV}.
$$

Drop the nonnegative fourth-order subtraction. Since $`h\le d/2`$ and $`B\ge (1-1/d)h(d-h)`$, the claimed bound follows. For a simple numerical gap, $`(d-2h)/(d-h)\le1-h/d`$ and $`h\ge1`$. Therefore the ratio is at most $`3+2/(d-1)-[1/h+h/d]`$, using $`2-1/h\ge1`$. It is at most $`3+2/(d-1)-2/\sqrt d`$. This margin can absorb an $`O(1/d)`$ relative error on the two angular derivatives.
