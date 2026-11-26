# Independent review of geometric-circle root counts

Agent-assisted review by Codex (`edge_referee`), 2026-11-26.

I accept the one-index factor-four count, the sharp $`16^{1/3}`$ threshold for angular monotonicity, and the bounds on the strict and weak disk counts at every geometric circle above the separately sharp uniform threshold $`9/4`$. All counts are with multiplicity. The balanced-array applications use the oriented second-quotient bounds for those coefficient sequences.

## One-index count

Let $`P(q)=\sum_{j=0}^D a_jq^j`$ have positive coefficients. For an internal index $`k`$ write $`v=\sqrt{a_{k-1}/a_{k+1}}`$, $`\Gamma_k=a_k^2/(a_{k-1}a_{k+1})`$, and $`t=\Gamma_k^{-1/2}`$. On the unit circle let $`F(z)=P(vz)/(a_kv^kz^k)`$. Both outward tails in $`F`$ start at magnitude $`t`$. When all coefficients are log-concave, each succeeding outward ratio is at most $`t`$. If $`t\le1/2`$, doubling the scaled weight at each successive step makes $`2^j w_j`$ nonincreasing. Its successive differences express each tail as a nonnegative combination, of total weight $`2t`$, of $`S_m(z)=\sum_{j=1}^m(z/2)^j`$ or its conjugate. Direct multiplication gives

$$
\mathrm{Re}(1+2S_m(z))\ge
\frac{3/4-3\cdot2^{-m-1}}{|1-z/2|^2}\ge0
\qquad (|z|=1).
$$

Thus $`\mathrm{Re}F\ge1-2t`$. Positivity holds for $`\Gamma_k>4`$ and also for $`\Gamma_k=4`$ if $`D\ge3`$. In the latter case at least one tail has a positive weight on a truncation with $`m\ge2`$, where the bound is strict. Hence $`P`$ has exactly $`k`$ zeros strictly inside the circle, no boundary zeros, and $`(-1)^kP(-v)>0`$. At equality in degree two both roots are at $`-v`$.

## Angular monotonicity and sharpness

Assume all second quotients are at least $`B=16^{1/3}`$. Write $`c_j`$ for the combined magnitudes of the normalized terms at distances $`j`$ on the two sides, each tail padded with zeros, and let $`b_j=jc_j`$. The successive ratios give $`c_{j+1}\le B^{-j-1/2}c_j`$, since the initial magnitude on either side is $`t\le B^{-1/2}`$. Therefore $`b_{j+1}\le b_j/2`$ by maximizing $`(1+1/j)B^{-j-1/2}`$ at $`j=1`$. Consequently $`d_j=b_j-2b_{j+1}+b_{j+2}\ge0`$ and finite summation gives

$$
-\frac{d}{d\theta}\mathrm{Re}F(e^{i\theta})
=\sum_{m\ge1}d_m\sum_{j=1}^m(m+1-j)\sin(j\theta).
$$

The inner sum is $`\big((m+1)\sin\theta-\sin((m+1)\theta)\big)/(2(1-\cos\theta))`$. It is strictly positive for $`0<\theta<\pi`$ because the geometric sum for $`\sin((m+1)\theta)/\sin\theta`$ has $`m+1`$ unit terms and nonconstant phases. Some $`d_m`$ is positive by the last nonzero $`b_m`$. This proves strict decrease and a unique circular minimum at $`-1`$. The sine-series positivity is classical. [Solodov, §§1–2](https://doi.org/10.1070/SM8633)

The reciprocal quartic with coefficients $`(B^{-2},B^{-1/2},1,B^{-1/2},B^{-2})`$ verifies sharpness when its parameter $`B`$ varies below $`16^{1/3}`$. Its three second quotients equal $`B`$, its middle radius is one, and the normalized real projection has derivative $`2B^{-1/2}-8B^{-2}<0`$ in $`x=\cos\theta`$ at $`x=-1`$. This breaks the minimum and monotonicity below the claimed threshold. This quartic is in the constant-curvature family studied by Handelman. [Handelman, §2](https://doi.org/10.1216/RMJ-2013-43-1-149)

## Sharp uniform threshold for the disk counts

For the weaker hypothesis $`G_i>9/4`$ for every internal $`i`$, set $`u=2/3`$ and let $`A(x)=1+\sum_{j\ge1}c_jT_j(x)`$ be the real projection with $`x=\cos\theta`$. The tail ratios give $`c_1<4/3`$, $`c_j\le2u^{j^2}`$ and $`c_j\le c_i u^{j^2-i^2}`$ for $`j\ge i\ge1`$.

On $`x\ge-1/\sqrt2`$, the derivative of the first quadratic $`1+c_1x+c_2(2x^2-1)`$ is at least $`c_1(1-16\sqrt2/27)>0`$. Its value at the left endpoint is at least $`1-4/(3\sqrt2)>2/35`$, where the final comparison follows by squaring from $`9800<9801`$. The remaining absolute tail is at most $`2u^9/(1-u^7)<2/35`$. Thus $`A`$ has a uniform positive lower bound there.

On $`-1\le x\le-1/\sqrt2`$, define $`h=-(2x^2-1)/(4x)\in[0,1/4]`$. The expression $`A+hA'`$ cancels the quadratic term. The linear part is at least $`1-3c_1/4>0`$, since $`x+h\ge-3/4`$. For $`y=-x`$, the cubic contributes with the factor

$$
T_3+hT_3'=\frac{8y^4-6y^2+3}{4y}\ge\frac12.
$$

The numerator is increasing in $`y^2\in[1/2,1]`$ and starts at $`2`$. All terms of degree four and higher have total absolute contribution less than $`c_3/2`$ when $`c_3>0`$, since $`|T'_j|\le j^2`$ and

$$
\sum_{j\ge4}(1+j^2/4)u^{j^2-9}
\le\frac{5u^7}{1-1/8}<\frac12.
$$

The successive ratio bound here is $`(29/20)u^9<1/8`$. When $`c_3=0`$ all higher terms are absent. Hence $`A+hA'`$ has a uniform strict positive lower bound on the left interval. At each zero of $`A`$, necessarily $`h>0`$ and $`A'>0`$. There can be at most one zero because every zero crosses upward as $`x`$ increases. Both uniform positive bounds persist at nearby radii by continuity of the real-projection polynomial and its derivative in $`x`$. This is sufficient even without global angular monotonicity.

If $`F(-1)>0`$, there is no real-projection zero and the curve lies in the right half-plane. This gives exactly $`k`$ interior roots and no boundary roots for $`P`$. The converse follows by parity from $`P(0)>0`$, the absence of nonnegative real roots and conjugation of nonreal interior roots.

If $`F(-1)<0`$ and the circle is root-free, the upper path from $`F(1)>0`$ to $`F(-1)<0`$ crosses the imaginary axis once. A crossing above or below zero gives the upper argument increment $`+\pi`$ or $`-\pi`$, respectively, by the continuous arguments on the right and left half-planes. Reflection gives the full winding $`+1`$ or $`-1`$ of $`F`$, hence a disk count of $`k+1`$ or $`k-1`$ for $`P`$. A crossing at zero gives a unique conjugate boundary pair, simple because the angular derivative of the real part is nonzero. For $`F(-1)=0`$ the sole boundary point is on the negative ray and $`A'(-1)>0`$. The real part then has a nonzero quadratic angular term, so the boundary root has multiplicity at most two.

The same half-plane argument gives counts in $`[k-1,k+1]`$ on nearby root-free radii. Taking one radius on each side with no intervening root moduli gives

$$
k-1\le N_{<}(v)\le N_{\le}(v)\le k+1.
$$

When the total boundary multiplicity is two, both extreme bounds are attained. For example $`1+5q/3+q^2`$ meets the strict curvature threshold and has both roots on its geometric circle. At equality in the uniform threshold, $`(1+q)^4`$ has least second quotient $`9/4`$ and open and closed counts $`0`$ and $`4`$ at its middle circle. Just below equality, the product of two distinct factors $`1+2\cos(\alpha)q+q^2`$ for small positive angles has four unit roots and $`P(-1)>0`$. Continuity of the three second quotients shows that no smaller uniform lower bound guarantees the positive-sign implication. The implication itself also holds at the closed threshold, since $`x+h>-3/4`$ for $`x>-1`$ still forces every interior crossing to be strictly upward.

## Application and provenance

For balanced arrays the orientation bound $`\log\Gamma_k>4d/(n+2)`$ meets the disk-count threshold whenever $`2d\ge(n+2)\log(3/2)`$. This includes every internal geometric circle in the finite million-row example, including the 5,518 root positions between its previously certified inner and outer intervals. The stronger angular-monotonicity property holds for $`3d\ge(n+2)\log 2`$. A positive normalized sign gives the exact central count. At a root-free circle with negative normalized sign the crossing direction selects the count. Consecutive exact counts with alternating signs isolate a simple negative root. For $`(n,d,r)=(10^8,100,50)`$ the earlier regular-row bound at $`k=49{,}999{,}936`$ is $`1199077934275800/859999987767059>139/100>\log4`$ and improves as $`k`$ increases. The local factor-four count upgrades the 64 outer sign intervals there to 64 simple negative roots. [Prior coefficient bound](https://github.com/ProgramComputer/open-math-research/blob/634a1e212f243289667f917cbb86664d2c81f127/topics/balanced-arrays/effective-upper-curvature/proof.md#stronger-exact-examples-from-the-raw-estimate)

Hutchinson and Kurtz impose factor four at every internal index for global conclusions. Pellet and the geometric-radius tropical criterion compare absolute magnitudes. Handelman's sector results have a different conclusion. The primary literature and indexed GitHub and X searches described in the [source record](literature.md) did not find the exact local count or the full-projection angular criterion. Priority remains undetermined. [Hutchinson](https://doi.org/10.1090/S0002-9947-1923-1501248-1) · [Kurtz](https://doi.org/10.1080/00029890.1992.11995845) · [Pellet](https://www.numdam.org/item/BSMA_1881_2_5_1_393_0/) · [Forsgård, Novikov and Shapiro](https://doi.org/10.1093/imrn/rnw118)
