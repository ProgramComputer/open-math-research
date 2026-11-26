# Independent review of the explicit aspect-three-to-four root count

Agent-assisted mathematical review by Codex (`edge_referee`), 2026-11-26.

I accept the rational-radius disk count for $`n\ge10^6`$, $`n/4\le d\le n/3`$, and each internal $`k`$ with $`1/8\le k/n\le7/8`$ satisfying $`n\Pr(\mathrm{Bin}(d,(k+3)/n)>r)\le1/100`$. I also accept the all-cap bound of $`\lceil n\sqrt{\log(100n)/(2d)}\rceil+4`$ roots left unproved simple and negative, and the claim of exactly 500,000 simple negative roots strictly inside the unit disk at $`(n,d,r)=(10^6,250000,127000)`$. I verified the numerical constants by exact rational comparisons.

## Full-circle projection

Let $`x=k/n`$, $`v=x(1-x)`$, $`w_0=x/(1-x)`$ and $`w_c=(k+1/2)/(n-k+1/2)`$. The latter is the odds at $`p_c=(k+1/2)/(n+1)`$. Directly,

$$
\log(w_c/w_0)=\log(1+1/(2k))-\log(1+1/(2(n-k))).
$$

The linear part is $`(1/2-x)/(nv)`$. Since both logarithm arguments are of the form $`1+y`$ with $`0\le y\le4/n`$, the remainder has absolute value at most $`16/n^2`$, which verifies the stated $`86/n^2`$ allowance. The unrestricted binomial ratio over $`j=1,2,3`$ uses the factors $`1-(i-1)/(n(1-x))`$ and $`1+i/(nx)`$. The error from linearizing their logarithms is at most $`64\sum_{i=1}^3[(i-1)^2+i^2]/n^2=1216/n^2`$. Reflection gives exactly the same estimate for negative $`j`$. The linear drift cancels against that of $`w_c/w_0`$. After multiplying by $`d`$, the error in the log term magnitude relative to the ideal $`e^{-aj^2}`$ is below $`.001`$ with $`a=d/(2nv)\ge1/2`$, since $`(1216+3\cdot86)/(3n)<.001`$.

The rows in the unrestricted ensemble at quota $`k+j`$ have binomial marginals with parameter $`(k+j)/n`$. Stochastic monotonicity and a row union bound give $`a_{k+j}/\binom n{k+j}^d\in[.99,1]`$ for all $`|j|\le3`$. Normalize the polynomial on $`|q|=w_c^d`$ by the unrestricted central magnitude $`\binom nk^d w_c^{dk}`$ and the phase of the central monomial. The capped term magnitudes in the block then differ from the ideal values by less than $`.011`$ relative to each ideal magnitude. Indeed $`.99e^{-.001}>.989`$ and $`e^{.001}<1.011`$. This estimate includes the center.

For $`u=e^{-a}`$ and $`t=\cos\varphi`$, the ideal seven-term projected real part is

$$
G(t)=1+2ut+2u^4(2t^2-1)+2u^9(4t^3-3t).
$$

Its derivative on $`[-1,1]`$ is at least $`2u(1-4u^3-3u^8)>0`$, using $`u<.607`$ and the rational inequality $`4(.607)^3+3(.607)^8<1`$. Thus the minimum is the parity sum at $`t=-1`$. That sum increases for $`a\ge1/2`$ because $`e^{3a}>4`$, and at $`a=1/2`$ it exceeds $`.032`$ using $`e^{-1/2}<.607`$, $`e^{-2}>.135`$ and $`e^{-9/2}<.012`$. The total ideal magnitude is below $`2.51`$ using $`e^{-2}<.136`$. Both unrestricted tails beyond distance three have total normalized magnitude at most

$$
\frac{2e^{-14a+.003}}{1-e^{-5a+.002}}<.003.
$$

Indeed the distance-three terms are at most $`e^{-9a+.001}`$, their ratios to distance two are at most $`e^{-5a+.002}`$, and log-concavity bounds all subsequent outward ratios by that last number. Capping can only shrink those tails in the chosen normalization. The full rotated projection is therefore strictly above $`.032-.011\cdot2.51-.003=.00139`$. A straight-line homotopy to the unrestricted central monomial keeps its normalized real part positive on the full circle. This gives exactly $`k`$ zeros inside and none on the circle. At the negative point it also gives sign $`(-1)^k`$.

## The missing block and root isolation

For $`x\le1/8`$, the orientation bound gives logarithmic curvature at least $`2/(1+8/n)+1/4>11/5>\log9`$. Here $`k\ge1`$ gives $`n-k+1\le n`$ for the second contribution. Reflection handles $`x\ge7/8`$. Each associated geometric test has normalized immediate neighbors $`\tau<1/3`$, and log-concavity bounds the absolute off-center mass by $`2\tau/(1-\tau)<1`$. This proves the same disk count and sign at the outer tests.

Put $`g=\sqrt{\log(100n)/(2d)}`$. Hoeffding certifies the central test whenever $`k+3\le nr/d-ng`$. The uncertified central indices lie in the single consecutive block $`nr/d-ng-3<k\le D-1`$ intersected with the central band. Its size is at most $`\lceil ng\rceil+3`$. In fact the floor identity $`\lfloor nr/d-ng-3\rfloor\ge D-\lceil ng\rceil-3`$ gives the slightly smaller bound $`\lceil ng\rceil+2`$. Either gives the claimed allowance. A small positive starting circle and sufficiently large ending circle supply indices $`0`$ and $`D`$. Strict disk counts order all the chosen circles, including different families. Two consecutive certified indices leave an annulus containing exactly one root counted with multiplicity. Their opposite signs also place that root on the negative real segment. If a block of $`m`$ indices remains, only the intervening annulus of $`m+1`$ roots is unproved simple and negative.

In the specified example the Hoeffding exponent for $`k=500000`$ is $`2\cdot250000(7997/10^6)^2>30>\log(100n)`$. Monotonicity certifies every lower central index, and the outer argument certifies the rest below it. At $`k=500000`$ the rational circle is the unit circle. Consecutive annuli give exactly 500,000 simple negative roots inside it, and the winding proof excludes boundary roots.

The earlier below-cap theorem gives an $`O(\sqrt{n\log n})`$ upper bound on the unproved roots in this aspect range by using $`D\le n`$. It has an unspecified absolute constant and retains useful dependence on $`D`$. The present result supplies a numerical bound from $`n=10^6`$ and counts at explicit rational or geometric radii. It leaves the behavior of the roots in the unproved annulus open. [Earlier below-cap theorem](../proof.md)

## Signed supplement on the final manuscript and the smaller exact disk

Codex (`edge_referee`), 2026-11-26. I checked the final manuscript, SHA-256 `62856ef43ef777840b9b8d2ee012064c00c65e1b42e769c582d4df5b13161587`, and replayed its checker, SHA-256 `bf4b9361892d1abe466d9eaaf88d4af3cf75925f10033df1682a8d1013000058`. The published-form result retains the valid $`+4`$ bound. I accept both exact disk counts and the lower bound of 501,926 simple negative roots from $`ng<6070`$. [Manuscript](paper.tex) · [Manuscript checker](verify.py)

At $`w=1/2`$ and $`k=333333`$, write $`B_j=\binom n{k+j}w^j/\binom nk`$ and $`T_j=B_j^d`$. I recomputed the local ratios independently of repeated squaring. In exact rational arithmetic, for $`t_j=1-B_j\in[0,1)`$, use $`t_j+t_j^2/2+t_j^3/3`$ as the lower bound on $`-\log B_j`$ and add $`t_j^4/(4(1-t_j))`$ for the upper bound. For either endpoint $`x`$ after multiplying by $`d`$, the exponential Taylor polynomial through degree 30 is a lower bound on $`e^x`$. The upper bound adds the first omitted term divided by $`1-x/32`$. Inverting the exponential bounds gives the following endpoints for $`10^9T_j`$.

| $`j`$ | Lower | Upper |
| ---: | ---: | ---: |
| $`-3`$ | 3,606,551 | 3,606,552 |
| $`-2`$ | 72,439,750 | 72,439,751 |
| $`-1`$ | 472,366,729 | 472,366,730 |
| $`0`$ | 1,000,000,000 | 1,000,000,000 |
| $`1`$ | 687,289,600 | 687,289,601 |
| $`2`$ | 153,355,498 | 153,355,499 |
| $`3`$ | 11,109,115 | 11,109,116 |

For $`C_j=T_j+T_{-j}`$, the unrestricted seven-term real projection as a polynomial in $`u=\cos\phi`$ is $`1+C_1u+C_2(2u^2-1)+C_3(4u^3-3u)`$. Its derivative is bounded below by $`C_1-4C_2-3C_3\ge .212328325`$. Its minimum is therefore attained on the negative ray and is at least $`.051423249`$. Each omitted tail is bounded using the last unrestricted term and the ratio of the third term to the second, giving combined loss below $`.001057`$. The Hoeffding exponent at quota $`k+3`$ exceeds 30, so the cap loss in the seven terms is below $`10^{-6}(1+C_1+C_2+C_3)<.000002401`$. The strictly positive full-circle margin exceeds $`.0503`$. Thus the winding is 333,333, the boundary has no root, and the sign at the negative intersection is negative. The previously checked unit-disk result makes every root in this smaller disk simple and negative.

## Signed supplement on the widened dimension range

Codex (`edge_referee`), 2026-11-26. I inspected the final TeX source with SHA-256 `a07936c7d1a73be51ee44df30fb9f22229bae19316b04beb3b48fac69f8f2114`. I accept Theorem 1 for every $`d\ge n/4`$ at $`n\ge10^6`$. The rational-radius theorem explicitly retains $`n/4\le d\le n/2`$. Its powered log error is at most $`(1216+3\cdot86)/(2n)=737/n<.001`$, and the Gaussian precision lower bound, cap loss, and tail comparison are unchanged. The separate angular refinement retains $`3\le n/d\le4`$. Both checker replays passed. [Final manuscript](paper.tex)

For $`d>n/2`$, the all-index curvature bound is $`\log G_k\ge4d/(n+2)>2n/(n+2)>3/2>\log4`$. At each geometric radius, both first outward magnitudes are $`\tau=G_k^{-1/2}<1/2`$ relative to the center. Log-concavity makes each outward tail decrease in magnitude, so its signed sum is at least $`-\tau`$ from the alternating pairing. The normalized value on the negative ray is strictly positive. Curvature also orders the geometric radii strictly, and with the constant and leading signs this gives all $`D`$ distinct negative zeros, which are simple by degree. For $`d\le n/2`$, the existing joining argument still gives the stated $`+4`$ bound. The two exact million-row disks remain within the checked range.
