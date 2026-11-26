# Independent review of the effective near-full root count

Agent-assisted mathematical review by Codex (`edge_referee`), 2026-11-26.

I accept the full root count under $`d^2\ge16384n\log(n+1)`$ and $`4n(d-r)\le d^2`$. The capped polynomial has $`D=\lfloor nr/d\rfloor`$ simple negative roots. The proof uses the published logarithmic mesh for the unrestricted polynomial and normalized log-concavity for the capped one. I checked the quantitative bounds, the strict Rouché comparisons, and the join of the two index ranges. [Unrestricted root mesh](../../dense-regime/below-cap/full-rank-root-stability.md) · [Normalized log-concavity](../../orientation-normalization.md)

For $`d\ge n`$ the normalized log-concavity bound gives $`\Gamma_k\ge(1+2/n)^{2d}>9`$ at every internal index when $`n\ge2`$, by the strict Bernoulli inequality at exponent $`n`$. The same monomial comparison below gives the root count. Degree at most one is immediate from positive coefficients. For $`d<n`$, the dimension hypothesis implies $`d>16384\log(n+1)>16384`$. Put $`k_0=n-\lfloor2d/5\rfloor`$. For $`1\le i<k_0`$ the midpoint $`T_i=\sqrt{\rho_i\rho_{i+1}}`$ lies between unrestricted root moduli. In particular $`N=n-i>2d/5`$.

## Tilt concentration at the midpoints

The unrestricted root factorization makes the quota $`K`$ at radius $`T_i`$ a sum of independent Bernoulli variables with probabilities $`p_j=T_i/(T_i+\rho_j)`$. Its complement $`H=n-K`$ has the same variance $`V=\sum_jp_j(1-p_j)`$. There are exactly $`i`$ unrestricted moduli below $`T_i`$. Comparing each $`p_j`$ to the indicator that $`\rho_j<T_i`$ costs at most $`2p_j(1-p_j)`$, so $`|\mathbb EH-N|\le2V`$.

For a mode $`m`$ of $`H`$ the mass at $`h`$ is proportional to $`\binom nh^d T_i^{-h}`$. Comparing each outward ratio with its first ratio at $`m`$ gives the right and left upper bounds $`((m+1)/(m+j+1))^d`$ and $`((m-j)/m)^d`$ from distance $`j`$ to $`j+1`$, whenever the respective step is in support. For $`L=\lceil\sqrt{(m+1)/d}\rceil`$, a block of $`L`$ ratios starting at distance at least $`L`$ is at most $`\exp[-dL^2/(m+1+L)]`$ on the right and $`\exp[-dL^2/m]`$ on the left when that side is present. The right exponent magnitude is at least $`d/(d+1)`$ because $`m+1\le dL^2`$ and $`L\ge1`$. The left exponent magnitude is at least one. At $`d\ge16384`$ both block ratios are below $`2/5`$, using $`d/(d+1)>19/20`$ and the cubic exponential Taylor lower bound at $`19/20`$.

For each of the two tails, send each index at distance at least $`(h+1)L`$ to its shadow $`hL`$ steps nearer to the mode. The images stay at distance at least $`L`$ and are disjoint across the two sides. Summing the pointwise block comparisons therefore gives $`\mathbb P(|H-m|\ge(h+1)L)\le(2/5)^h`$ without a factor of two. Upper integer blocks in the second moment give

$$
\mathbb E(H-m)^2\le L^2\left(1+\sum_{h\ge0}(2h+3)(2/5)^h\right)=\frac{74}{9}L^2<9L^2\le19(1+m/d).
$$

The last inequality follows from $`L^2\le2(1+(m+1)/d)`$ and $`d\ge18`$. Cauchy–Schwarz, $`V\le\mathbb E(H-m)^2`$, and the mean-index bound give $`|m-N|\le43(1+m/d)`$. Solving for $`m`$ gives $`m\le(N+43)/(1-43/d)<6N/5`$ throughout the range. Consequently $`V\le19(5/2+6/5)N/d<72N/d`$, which also gives $`V\le N/192`$ and, by $`2V\le144N/d`$, $`\mathbb EH\ge .99 N`$.

## Strict perturbation bound

On $`|z|=T_i`$, write $`y_j=\log(\rho_j/T_i)`$. The logarithmic mesh gives $`|y_j|\ge\pi/\sqrt{n(n+1)}>1/n`$. The normalized absolute contribution of the $`j`$th factor is at least $`\tanh(|y_j|/2)`$. For $`|y_j|\le1`$ this is at least $`1/(4n)`$, while $`p_j(1-p_j)>1/6`$. One has $`\log(4n)\le(4/3)\log(n+1)`$ for $`n\ge64`$, so each such logarithmic loss is bounded by $`8p_j(1-p_j)\log(n+1)`$. For $`|y_j|>1`$, put $`a=e^{-|y_j|}<3/8`$. Then

$$
\log\frac{1+a}{1-a}\le\frac{2a}{1-a^2}=\frac{2(1+a)}{1-a}\thinspace{}p_j(1-p_j)<8p_j(1-p_j).
$$

This proves $`|F(z)|/F(T_i)\ge\exp[-8V\log(n+1)]`$ on the full circle.

For the Bernoulli sum $`H`$, the deficit of $`(9/10)N`$ below its mean is at least $`(9/100)N`$. Bernstein's exponent is at least

$$
\frac{(9/100)^2}{2(1/192+3/100)}N>\frac N{10}.
$$

Given $`H\ge .9N`$, put $`M=dN/n`$. The number of omitted entries in any specified row is binomial, with mean $`\mu=dH/n\ge .9M`$. The required minimum number of omissions $`c=d-r`$ satisfies $`c\le d^2/(4n)<(5/8)M`$ because $`N>2d/5`$. The relative lower-tail Chernoff bound gives an exponent at least $`(\mu-c)^2/(2\mu)`$. This expression increases with $`\mu`$ when $`\mu>c`$ and decreases with $`c`$, so its uniform lower bound is $`(121/2880)M>M/24`$. Union over rows and add the Bernstein contribution, which is at most $`e^{-M/24}`$ since $`d<n`$. The total overflow probability is at most $`(n+1)e^{-M/24}`$. The triangle inequality applied to the nonnegative coefficient losses bounds $`|P(z)-F(z)|/F(T_i)`$ by this probability. The dimension condition makes it strictly less than $`\exp[-8V\log(n+1)]`$, since

$$
M/24-576(N/d)\log(n+1)-\log(n+1)
\ge\left[(16384/24-576)(N/d)-1\right]\log(n+1)>0.
$$

Rouché now gives exactly $`i`$ roots inside the midpoint circle and none on it. At the negative intersection, strict real comparison preserves the sign $`(-1)^i`$ of $`F(-T_i)`$.

## Upper sector and the join

For $`k_0\le k\le D-1`$, the coefficient curvature is strictly above $`(1+1/(n-k))^d`$ by the normalized log-concavity bound. Its logarithm exceeds $`12/5`$ because $`n-k\le2d/5`$ and $`d/(2d/5+1)>12/5`$. The exponential Taylor lower bound through degree four at $`12/5`$ exceeds nine. At $`x_k=\sqrt{a_{k-1}/a_{k+1}}`$ the two immediate neighbors each have magnitude $`\tau=\Gamma_k^{-1/2}<1/3`$ relative to the central term. Log-concavity makes each outward ratio at most $`\tau`$. Hence the absolute sum of all off-center terms on $`|z|=x_k`$, divided by the central magnitude, is at most $`2\tau/(1-\tau)<1`$. Rouché against that monomial gives exactly $`k`$ roots inside and none on the circle. At $`-x_k`$ the strict comparison likewise gives sign $`(-1)^k`$.

The degree satisfies $`D=n-\lceil n(d-r)/d\rceil`$, so $`D-k_0\ge3d/20-2>1`$. Thus both index ranges are present, and the midpoint ranges end at $`i=k_0-1`$. Nested disks and their strict root counts force $`T_{k_0-1}<x_{k_0}`$ and order all of the remaining geometric radii. There is exactly one signed test for each index from $`1`$ to $`D-1`$. The signs at zero and negative infinity are positive and $`(-1)^D`$. Consecutive sign changes give $`D`$ distinct strictly negative zeros, so the degree forces all of them to be simple. All displayed numerical comparisons were also checked with exact rational arithmetic.
