# The sign at a geometric node of quadratic aspect

Let $`d\to\infty`$, $`n/d^2\to\alpha\in(0,\infty)`$, and $`k/n\to x\in(0,1)`$. Assume $`\liminf r/d>x`$ and $`r<d`$. Let $`t_k=\sqrt{a_{k-1}/a_{k+1}}`$ be the geometric node of the capped array polynomial. There are positive normalizations $`C_{n,d,r,k}`$ for which

$$
C_{n,d,r,k}(-1)^kP(-t_k)\longrightarrow
\cos\negthinspace{}\left(\frac{\alpha\pi^3}{6}x(1-x)(1-2x)\right).
$$

The proof specifies the normalization before taking the limit. In particular, for $`n=4d^2`$, $`k=d^2`$ and every $`\lceil d/2\rceil\le r<d`$, the geometric sign is wrong for all sufficiently large $`d`$. The polynomial itself has simple negative zeros there by the quadratic-aspect theorem. The sign reversal gives an obstruction to extending the polynomial-dimension proof at its current choice of test points. [Critical-aspect root theorem](../critical-aspect/README.md) · [Independent agent-assisted calculation](square-phase-review.md)

## Proof

Under the uncapped uniform measure for quota $`j`$, each column is independently a uniform $`j`$-subset of rows. The load of a specified row has distribution $`\mathrm{Bin}(d,j/n)`$. For $`j=k\pm1`$ the fixed gap below $`r/d`$ gives a probability at most $`e^{-cd}`$ of a cap violation in this row by the binomial Chernoff bound. A union bound over rows shows $`a_j/\binom nj^d=1+O(ne^{-cd})`$. Consequently $`v=t_k^{1/d}`$ differs from the uncapped odds $`v_0`$ by $`O(ne^{-cd}/d)`$ in log odds, where, writing $`x_d=k/n`$,

$$
v_0^2=\frac{k(k+1)}{(n-k)(n-k+1)},\qquad
p_0=\frac{v_0}{1+v_0}=x_d+\frac{1-2x_d}{2n}+O(n^{-2}).
$$

At odds $`v`$, the actual size $`S`$ of a tilted row is a binomial of parameters $`d,v/(1+v)`$ conditioned on $`S\le r`$. The removed mass is exponentially small. This gives $`\mu/d\to x`$, $`V/d\to x(1-x)`$ and $`a\to x(1-x)`$ for its mean, variance and transverse precision. Write $`t=\pi/d`$ and $`H(v)=\sum_{s=0}^r\binom ds v^s`$. Since $`r-\mu`$ grows linearly in $`d`$ and $`V\to\infty`$, the single-chart and remainder estimates in the critical-aspect proof give, for the principal Gaussian $`G_t`$ of the actual row law,

$$
P(-v^d)/H(v)^n=2\Re G_t+o(|G_t|).
$$

Specifically the relative principal-chart error is $`O(d^{-1/2})`$, and the other near labels have a summable Gaussian bound with parameter $`nV/d^2\asymp d`$. These bounds on absolute errors hold at the chosen tilt before any condition is imposed on the principal phase. Take $`C_{n,d,r,k}=1/(2H(v)^n|G_t|)`$. [Chart bounds at arbitrary interior tilt](../critical-aspect/critical-aspect-angular-nodes.md)

Along angles from zero to $`t`$, replacing the capped row law by the binomial at $`v_0`$ changes its characteristic function $`\phi`$ and its complex precision $`a(t)`$ by exponentially small amounts. The test functions for their numerators are bounded, the log-odds displacement is exponentially small, and their binomial values are bounded away from zero in modulus on the segment. Both arguments therefore give an $`o(1)`$ total error even after multiplication by $`n`$ or $`d`$. For the binomial, $`\phi(t)=(1+v_0e^{it})^d/(1+v_0)^d`$ and $`a(t)=v_0e^{it}/(1+v_0e^{it})^2`$. Thus

$$
\arg G_t=(nd+d-1)\arg(1+v_0 e^{it})-(d-1)t/2+o(1)
$$

in the branches continued along the segment. The argument in the first term is $`p_0t-p_0(1-p_0)(1-2p_0)t^3/6+O(t^5)`$ by Taylor expansion of the binomial logarithm. The linear terms, after subtracting $`k\pi`$, give $`\pi(np_0-k)+\pi(1-1/d)(p_0-1/2)=o(1)`$. The cubic term tends to $`-\alpha\pi^3 x(1-x)(1-2x)/6`$, and the fifth-degree error tends to zero. Taking the cosine proves the limit.

For $`\alpha=4`$ and $`x=1/4`$, the absolute phase displacement is $`\pi^3/16`$, strictly between $`\pi/2`$ and $`\pi`$. If the negative sign failed for arbitrarily large $`d`$ at some listed cap, a sequence of such caps would satisfy the same strict gap and give the negative limiting cosine, a contradiction. $`\square`$

For fixed dimension, a different asymptotic gives an equal limiting proportion of right and wrong geometric signs in the bulk. Abel, Gawronski and Neuschel study the asymptotic behavior of binomial polynomials with a fixed exponent. Here the exponent grows and the row cap may vary. [Fixed-dimension result](https://github.com/ProgramComputer/open-math-research/blob/8a0a986e6baeed69b30de189e75c02fd2c8cb955/topics/balanced-arrays/geometric-centers/bulk-center-density.md) · [Abel–Gawronski–Neuschel](https://doras.dcu.ie/31197/1/Binomialpolynomials.pdf)
