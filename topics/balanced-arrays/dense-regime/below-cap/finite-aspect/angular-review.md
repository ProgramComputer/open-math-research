# Review of the stronger finite angular and rational disk counts

Independent review by the quota referee, 2026-11-26. I accept the angular refinement with normalized expected overflow at most $`10^{-6}`$ and the rational-radius refinement with bound $`1/100`$. Each proves the exact disk count $`k`$ and absence of boundary zeros. The argument concerns a single quota under its stated condition. This note reuses the phase-branch and coefficient calculations checked in the [earlier review](https://github.com/ProgramComputer/open-math-research/blob/de9c27e1544db4c7cfea3e090c5cf8893163daad/topics/balanced-arrays/angular-node-order/bounded-aspect/finite-rare-overflow-review.md).

Write $`n\ge10^6`$, $`3\le n/d\le4`$, $`x=k/n\in[1/4,3/4]`$, and $`1\le r<d`$. Put $`\varepsilon=\Pr(\mathrm{Bin}(d,(k+3)/n)>r)`$ and $`\eta=n\varepsilon`$. All seven coefficients $`a_{k+j}`$, $`|j|\le3`$, satisfy

$$
(1-\eta)\binom n{k+j}^{d}\le a_{k+j}\le\binom n{k+j}^{d}.
$$

For a fixed quota, choose independently one uniform subset of the prescribed size for each column. A specified row has the corresponding binomial load. Its overflow probability is increasing in the quota, and union over the rows gives the bound. In particular $`a_{k+3}>0`$ under either hypothesis, verifying that $`k`$ is internal.

## The angular bracket when $`\eta\le10^{-6}`$

Let $`p_c=(k+1/2)/(n+1)`$ and $`p_\pm=p_c\pm(100/n^2+10^{-4}/n)`$. Both bracketing probabilities satisfy $`|p_\pm-x|<1/n`$ and $`p_\pm\in[1/5,4/5]`$, so their row overflow probabilities are at most $`\varepsilon`$. The earlier phase-branch calculation on $`0\le t\le\pi/d`$ applies unchanged. Indeed $`\varepsilon\le10^{-6}/n\le10^{-12}`$ keeps the radial and precision quotient perturbations in the same disks, and the radial and precision phase errors are bounded by $`5\varepsilon`$ and $`64\varepsilon`$. Thus the capped phase differs from the uncapped phase by at most $`100n\varepsilon\le10^{-4}`$.

The linearized uncapped phase is $`L(p)=\pi[(n+1-1/d)p-(d-1)/(2d)]`$. At $`p_c`$ its distance to $`k\pi`$ is below $`7/n`$, and the uncapped cubic error is below $`26/n`$. The change in $`L(p)`$ from $`p_c`$ to either bracket endpoint has magnitude at least $`300/n+3\cdot10^{-4}`$. The total error $`33/n+10^{-4}`$ is smaller. The ordered exact angular tilt is therefore inside this bracket.

Set $`v=x(1-x)`$ and $`w_0=x/(1-x)`$. For every $`p`$ in the bracket, $`|p-x|\le1/n`$ and

$$
\left|p-x-\frac{1/2-x}{n}\right|\le\frac{101}{n^2}+\frac{10^{-4}}n .
$$

The logit derivative at $`x`$ is below six and the absolute second derivative is below 50 on the connecting segment. With $`w=p/(1-p)`$, this gives

$$
\left|\log(w/w_0)-\frac{1/2-x}{nv}\right|
\le\frac{650}{n^2}+\frac{.0006}{n}.
$$

The seven-term binomial ratio calculation of the earlier proof has error at most $`400/n^2`$ before powering and cancels the linear drift. For the capped coefficients the log correction relative to the center costs at most $`2\eta\le2\cdot10^{-6}`$. Thus, for $`1\le|j|\le3`$, $`T_j=a_{k+j}w^{d(k+j)}`$ satisfies

$$
\left|\log(T_j/T_0)+aj^2\right|
\le \frac{2350}{3n}+.0006+2\cdot10^{-6}<.002,
\qquad a=\frac{d}{2nv}\ge\frac12 .
$$

This is valid throughout the bracket. It includes the rational tilt $`w_c=(k+1/2)/(n-k+1/2)`$ and the true angular tilt.

## Real projection and tails on the entire circle

Let $`u=\cos\varphi`$ and write the model after removing the central phase as

$$
G_a(u)=1+2e^{-a}u+2e^{-4a}(2u^2-1)+2e^{-9a}(4u^3-3u).
$$

On $`-1\le u\le1`$ its derivative is at least $`2e^{-a}(1-4e^{-3a}-3e^{-8a})>0`$. At $`a\ge1/2`$ the positivity follows from $`e^{3/2}>40/9`$ and $`e^4>30`$. Hence its minimum lies at $`\varphi=\pi`$. The earlier seven-term estimate gives $`G_a(-1)>.032`$.

On the actual circle the real projection of the seven terms differs from the model by less than $`.018`$, since each of the six noncentral normalized terms has absolute error below $`.003`$. Global log-concavity gives that ratios decrease going outwards on either side. Beyond the seven terms the ratio is bounded by $`T_{\pm3}/T_{\pm2}\le e^{-5a+.004}<.09`$, and $`T_{\pm3}/T_0<.013`$. This gives total omitted absolute mass less than $`2(.013)(.09)/(1-.09)<.003`$, including a tail cut off by a support endpoint. The real part of the normalized polynomial after removing the central phase is therefore greater than $`.032-.018-.003>.01`$ on the whole circle.

To count roots, let $`R=w^d`$. For $`|z|=1`$, the normalized function $`P(Rz)/(T_0z^k)`$ has strictly positive real part. The straight-line homotopy from $`T_0z^k`$ to $`P(Rz)`$ is nonzero on the circle because the same normalized projection of every homotopy member is positive. It follows that the disk $`|q|<R`$ contains exactly $`k`$ zeros counted with multiplicity, with no zeros on the circle. At its negative point the sign is $`(-1)^k`$. This works for every radius in the tilt bracket.

## Rational radius with $`\eta\le1/100`$

At $`p=p_c`$ the logit error after subtracting the linear drift is even below $`4/n^2`$, since $`|p_c-x|\le1/(4n)`$ and its error from the linear shift is at most $`1/(4n^2)`$. The unrestricted seven-term log errors at $`w_c`$ are therefore below $`.001`$. Normalize this time by $`\binom nk^d w_c^{dk}`$, without dividing by the possibly reduced capped central coefficient. The validity interval $`[.99,1]`$ multiplies every unrestricted term in the block, including the central term. Each capped normalized term differs from its model by less than $`.011`$ times its ideal magnitude. For the lower bound use $`.99e^{-.001}>.99(1-.001)>.989`$ and for the upper bound use $`e^{.001}<1.002`$.

The total ideal magnitude is less than $`2.51`$ by $`e^{-1/2}<.607`$, $`e^{-2}<.136`$, and $`e^{-9/2}<.012`$. The absolute normalized unrestricted tails are below $`.003`$, by the same outward-ratio calculation as above with smaller log error. The capped tails are bounded termwise by the unrestricted tails with this normalization. Thus on the full rational test circle the real projection is greater than

$$
.032-(2.51)(.011)-.003=.00139>.001.
$$

The monomial homotopy gives the same disk count and strict sign. This branch does not use the angular bracket.

## Independent unit-circle comparison at aspect four

Suppose $`n=4d`$ and $`m=k=n/2`$. Write $`B_j=\binom n{m+j}^d`$ and $`F(q)=\sum_i\binom ni^d q^i`$. By symmetry $`B_{-j}=B_j`$. The first outward log-ratio drop at zero is at least $`n/(2n+4)>.49`$. Every subsequent log-curvature is at least $`4d/(n+2)>.98`$. Therefore $`B_j/B_0\le e^{-.49j^2}`$. In particular,

$$
\frac{F(1)}{B_0}
\le 1+2\left(e^{-.49}+\frac{e^{-1.96}}{1-e^{-2.45}}\right)<3.
$$

The seven central log errors relative to $`e^{-j^2/2}`$ are at most $`304/(4n)<10^{-4}`$. This gives signed normalized sum above $`.032-6\cdot.0002>.030`$, and the omitted signed tails are nonnegative by pairing. Here $`m=2d`$ is even. Thus $`F(-1)/F(1)>1/100`$. Since $`F`$ has all negative roots, the true minimum reference modulus on the unit circle is $`F(-1)`$.

At the positive radius one the unrestricted quota $`K`$ has mass $`B_{K-m}/F(1)`$. Its probability of $`|K-m|>5`$ is at most $`2e^{-.49\cdot36}/(1-e^{-.49\cdot13})<4\cdot10^{-7}`$. For a quota at most $`m+5`$, the row overflow probability is at most that at $`p'=(m+5)/n`$. Relative to $`p=(m+3)/n`$, every binomial atom grows by at most $`(p'/p)^d\le e^{d(p'-p)/p}\le e<3`$. Under $`\eta\le10^{-6}`$ the union over rows costs less than $`3\cdot10^{-6}`$. The total normalized coefficient loss at radius one is therefore below $`4\cdot10^{-6}`$, strictly less than $`F(-1)/F(1)`$. Rouché gives the same disk count for $`P`$ and $`F`$. The latter is $`m=n/2`$ by reciprocity and absence of unit-circle roots.

For $`n=10^6,d=250000,r=127000,k=500000`$, the exact Hoeffding exponent is $`2d(127000/d-(k+3)/n)^2>30`$. The Taylor lower bound $`e^5>100`$ gives $`e^{30}>10^{12}`$ and thus $`\eta<10^{-6}`$. This example has exactly 500,000 roots strictly inside the unit disk and no boundary zeros. The direct rational method already gives this count because $`w_c=1`$.

## Rational arithmetic check

Run the accompanying [Python check](verify-angular.py) with the standard library. It verifies all numerical comparisons used above. Lower Taylor bounds certify the needed negative-exponential upper bounds. Each monotone-in-height estimate is checked at $`n=10^6`$.
