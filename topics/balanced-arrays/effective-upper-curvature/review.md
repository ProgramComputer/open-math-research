# Independent review of the effective upper-edge inequality

Signed by agent-assisted reviewer four_blind, 2026-11-26.

**Verdict.** The written estimate, its sufficient conditions and the half-line root count hold for actual balanced-array polynomials. I found no gap. Using the raw lower bound rather than the simpler sufficient conditions certifies more roots in both requested examples.

## Switching and feasibility

Fix the entries outside the two selected columns. If the current excess is $`\Delta\ge0`$, the number of one-slot rows is $`2X+\Delta`$. The old fiber has $`\binom{2X+\Delta}{X}`$ completions and the new fiber has $`\binom{2X+\Delta}{X-1}`$. Any new nonempty fiber has at least $`\Delta+2`$ one-slot rows, hence also has an old completion. Thus the ratio is exactly the expectation of $`X/(X+\Delta+1)`$ under the old uniform measure, including the fibers with $`X=0`$.

The two stability applications have different fixed margins and both work. For the distinguished row, a term $`\prod(x_j+z_j)`$ chooses a hole when it uses $`x_j`$. The extraction after multiplying by $`e_r(z)^{B-1}`$ forces precisely $`r`$ choices of $`z_j`$. Differentiating for coefficient extraction and specializing at zero preserves real stability or gives the zero polynomial, excluded by feasibility. Rayleigh at unit weights gives negative correlation of the two holes, hence also of the two complementary occupancies. Summing over rows gives $`\mathbb EX\ge u_j(1-u_i/B)`$.

For the conditional variance, condition on an occupied row set $`I`$ for column $`i`$. A product of elementary symmetric polynomials in the row variables, one factor per remaining column other than $`j`$, enumerates all their supports. Multiply by $`\prod_a(x_a+z_a)`$ for column $`j`$ and extract the residual row exponents $`r-\mathbf1_I(a)`$. The total exponent forces the quota $`u_j`$ in column $`j`$. Mark just the holes outside $`I`$ with a common variable and set the other marks to one. Reversal with exponent $`B-|I|`$ gives the generating polynomial of $`X`$, still real-rooted with nonpositive zeros, allowing monomial factors. Its normalized factors are Bernoulli generating functions. The conditional count law does not depend on which $`I`$ of size $`u_i`$ is selected, by permutation of row labels. Therefore $`\mathrm{Var}(X)\le\mathbb EX`$ unconditionally. With $`m=\mathbb EX>0`$, Cauchy–Schwarz yields

$$
\mathbb E\frac{X}{X+\Delta+1}
\ge\frac{m^2}{\mathbb E[X^2+(\Delta+1)X]}
\ge\frac{m}{m+\Delta+2}.
$$

The applications have $`m>0`$, so none of the divisions involves zero.

Choose any coordinate-balancing path from the target margin vector to a balanced vector as an integer-vector path. This does not require target feasibility. The balanced terminal vector is feasible by cyclic allocation. Reversing the path and applying the positive ratio at each step proves all intermediate vectors feasible. The width bound persists since forward balancing never goes outside the extrema of the endpoints of the move. In that box the low margin is at least $`Bp/2`$ and the high margin at most $`B(1+p)/2`$, so $`m\ge L=Bp(1-p)/4>0`$. The squared-deviation increase on an outward move is $`2(\Delta+1)\ge\Delta+2`$. Adding the log losses gives the claimed count comparison.

## Profile average and curvature

For each labeled row-size profile, choose $`B`$ full rows and permute them first. The last $`M`$ rows can have different sizes. Their columns within a row need not be independent, because the energy uses a sum of coordinate squares. For each column separately, last-row indicators are independent with means $`s/d`$ in rows of size $`s`$. The profile's fixed total makes $`\mathbb E(k'-W_i)=Bp`$ exactly. Thus the expected energy is $`\sum_s s(1-s/d)`$ over the last rows, including multiplicities. With $`s=r-j`$, expansion gives

$$
s(1-s/d)=dp(1-p)+(2p-1)j-j^2/d\le dp(1-p)+j.
$$

Since $`dp(1-p)=r(d-r)/d\ge1/2`$ and the total deficit is at most $`M`$, the expected energy is at most $`3Mdp(1-p)`$. Jensen for the convex function $`\exp(-H/L)`$ then gives the claimed common left factor, including if all rows in one quota are full. Scalar profile weights are positive labeled counts, so averaging does not change either uniform bound. The two factors from $`a_k`$ explain the coefficient $`24`$ in the curvature error.

For the scalar comparison, $`e\ge d`$ at an internal quota. Put $`v_e=\binom{n+e-1}{e}`$. The scalar normalization gives curvature at least $`\log(v_e^2/(v_{e-d}v_{e+d}))`$. For $`x=e-d+j`$, $`1\le j\le d`$, the summand in this last log curvature is

$$
\log(1+d/x)-\log(1+d/(x+n-1))
=\int_0^d\frac{n-1}{(x+t)(x+t+n-1)}\thinspace dt.
$$

Here $`1\le x\le e`$, so it is at least $`(n-1)\log(1+d/e)/(n+M-1)`$. This also covers $`e=d`$, whose lower scalar quota is zero. Under the three sufficient inequalities the written bound is at least $`3d^2/(8M)\ge3/2>\log4`$. All conditions are monotone toward the upper quota since $`M`$ decreases and $`B`$ increases.

## Signs and examples

Ordinary global log-concavity gives nonincreasing successive coefficient ratios, so the magnitudes at each geometric point decrease outward on each side of its center term once the immediate neighbor is less than half. The normalized alternating tails beyond those neighbors are nonnegative by pairing from distance two outward. Both immediate neighbors have the same magnitude ratio $`\Gamma_k^{-1/2}<1/2`$ to the center. The sign is therefore strict. At successive qualifying nodes the radii increase strictly since $`t_{j+1}/t_j=\sqrt{\Gamma_j\Gamma_{j+1}}>1`$. The limiting sign at negative infinity is $`(-1)^D`$. Consecutive finite intervals and the final infinite interval give $`D-k`$ disjoint open intervals, all strictly left of $`-t_k`$.

| $`(n,r,d)`$ | $`D`$ | First quota from the three sufficient conditions | Number of certified roots | Raw log lower bound there |
| --- | ---: | ---: | ---: | ---: |
| $`(20000,10,20)`$ | 10000 | 9999 | 1 | 12.87334784 |
| $`(100000000,50,100)`$ | 50000000 | 49999976 | 24 | 4.02209590 |

For these examples $`e=d(D-k)`$, so the exact sufficient-condition check uses integer arithmetic. In the first example $`D-k=1`$ passes and $`D-k=2`$ fails the inequality $`192M^2\le Bd`$. In the second $`D-k=24`$ passes and $`D-k=25`$ fails $`4M\le d^2`$.

The raw estimate separately certifies 4 and 64 roots, respectively. At $`D-k=4`$ and $`64`$, respectively, even replacing $`\log(1+d/e)`$ by its lower bound $`2d/(2e+d)`$ gives values larger than $`1.39>\log4`$. The first main hypothesis still holds. At $`D-k=5`$ and $`65`$ respectively, replacing the log by its upper bound $`x-x^2/2+x^3/3`$, with $`x=d/e`$, already gives values below $`1.38<\log4`$. The raw bound decreases as $`M`$ increases throughout its applicable range. The rational inequalities $`1.38<\log4<1.39`$ follow from the series for $`\log2`$ at inverse hyperbolic tangent argument $`1/3`$ using the first two terms and a geometric upper bound on the remainder.

## Simple outer zeros

The added corollary also holds. Replacing $`4M\le d^2`$ by $`6M\le d^2`$ improves the same lower bound to $`9/4>\log9`$. On the entire circle $`|q|=t_k`$, global log-concavity bounds the absolute value of a term at distance $`j`$ from the center relative to the center by $`\Gamma_k^{-j/2}`$. The sum over both sides is at most $`2/(\sqrt{\Gamma_k}-1)<1`$. Rouché therefore gives exactly $`k`$ zeros inside the circle, counting multiplicities, and no zeros on it. The earlier sign intervals supply $`D-k`$ distinct negative zeros outside that circle. Since the polynomial has degree $`D`$, these account for every outside zero and are all simple. The strengthened condition first holds at $`k=9999`$ in the first example and at $`k=49{,}999{,}985`$ in the second, giving one and fifteen simple outer zeros, respectively.
