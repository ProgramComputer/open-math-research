# Finite high-rank sector certificate for balanced arrays

**Result.** For $`36\le n<1024`$, $`d\ge\lceil n/4\rceil`$, and $`r\ge\lceil9d/10\rceil`$, the original balanced-array polynomials have only simple negative zeros. The finite replay below uses the available full-cap and corank-one endpoints and the normalized log-concavity theorem. Previously checked small rows can be handled separately. No coefficient vector is counted in full.

Let $`p_k=a_k/\binom nk^d`$, let $`D=\lfloor nr/d\rfloor`$, and let

$$
g_k=\left(\frac{(k+1)(n-k+1)}{k(n-k)}\right)^d, \qquad
\Gamma_k=\frac{a_k^2}{a_{k-1}a_{k+1}}\ge g_k
$$

at internal quotas. The inequality is the normalized log-concavity theorem. All coefficients up to $`D`$ are positive, since successive columns may use successive cyclic blocks of $`k`$ rows, making all row occupancies at most $`\lceil dk/n\rceil`$. A strict factor-four bound at an internal $`k`$ gives the sign at the geometric center $`t_k=\sqrt{a_{k-1}/a_{k+1}}`$. At the endpoints use zero and a sufficiently large negative argument. Strict log-concavity gives strictly ordered centers. These signs certify the full degree of distinct roots.

At an active quota, put $`\tau=\Gamma_k^{-1/2}`$. Both immediate terms have normalized magnitude $`\tau`$. In direction $`e\in\{-1,1\}`$ the combined second and third terms, with the later alternating remainder, contribute at least

$$
\frac{\tau^2}{\Gamma_{k+e}}
\left(1-\frac{\tau}{\Gamma_{k+e}\Gamma_{k+2e}}\right).
$$

The remainder has the sign of its first term because strict log-concavity makes the term magnitudes decrease outward. The code checks that all active quotas permit both third terms at the lowest considered cap.

## First pass

For any cap at least $`r_0`$, set $`l_k=\max(0,1-n\thinspace \mathbb P(\mathrm{Bin}(d,k/n)>r_0))`$, so $`l_k\le p_k\le1`$. The exact binomial tail is bounded above by evaluating its finite sum with upward rounding. On the active quotients the code checks a certified lower bound $`G\le g_k`$ is at least $`9/4`$. Therefore $`\tau\le2/3`$. A lower bound for the normalized signed value is $`1-2\tau+C\tau^2`$ with any $`0\le C\le1`$ at most

$$
\sum_{e=\pm1}
\frac{l_k l_{k+2e}}{g_{k+e}}
\left(1-\frac{2}{3g_{k+e}g_{k+2e}}\right).
$$

This quadratic is decreasing for $`0\le\tau\le1`$, so it suffices that $`1-2/\sqrt G+C/G>0`$. Squaring the equivalent positive-side inequality gives $`(G+C)^2>4G`$, the test in the binary64 checker.

The checker advances each elementary arithmetic operation with IEEE binary64 outward rounding. It checks round-to-nearest, uses the adjacent representable value in the required direction after every operation, and uses compiler flags that disallow contraction and fast-math. Integer arguments and integer products used when building the base ratios are exactly representable throughout this range. The curvature base reaches its minimum at the center since it is $`1+(n+1)/(k(n-k))`$. For fixed $`n`$, once the lower bound on this minimum to power $`d`$ exceeds four, all larger $`d`$ are automatically separated. The independent orientation bound also covers $`d\ge n`$.

## Refinement

The first pass at $`r_0=\lceil9d/10\rceil+1`$ covers every relevant pair. For the 100 pairs where the first pass at $`r_0=\lceil9d/10\rceil`$ is incomplete, only that exact minimum cap remains. Bound its $`p_k`$ by exact integer Bonferroni sums, using the prescribed-row defect histogram in [defect-histogram proof](https://github.com/ProgramComputer/open-math-research/blob/114696f2f69429411c6cd4f11955aee963d5320d/topics/balanced-arrays/curvature-compensation/defect-histogram.md). For an additional upper bound, negative association of the independent column indicators yields $`p_k\le(1-\mathbb P(\mathrm{Bin}(d,k/n)>r_0))^n`$. This upper bound applies to the exact cap under refinement.

Use the resulting rational intervals to bound each needed $`\Gamma_i`$ from both sides, clipping its lower bound below by $`g_i`$. A dyadic upper bound $`T`$ on $`\Gamma_k^{-1/2}`$ then gives the correction $`C`$ by bounding each summand in the displayed second–third term formula. The exact minimum of $`1-2\tau+C\tau^2`$ over $`0\le\tau\le T`$ is its endpoint value if $`CT\le1`$, and $`1-1/C`$ otherwise. This uses only rational arithmetic and an integer square root. The largest Bonferroni order needed anywhere is eight, so no whole-array count is required.

## Replay

The binary64 and independent integer mantissa implementations give identical miss files. The first pass covers 50,724 of 50,824 nontrivial pairs, rechecking 12,281,490 active quotas. The offset-one pass covers all 50,536 nontrivial pairs. The separate 95% pass covers all 50,136 nontrivial pairs. The refinement covers the 100 missed minima, with 37 certified at order one, 47 at order three, 14 at order five and two at order eight. It checks every quota between the first and last miss for each pair.

The integer-only checker stores a nonzero value as a 48-bit normalized mantissa times a signed power of two, with a separate zero value. Alignment floors or ceilings the shifted mantissa. Subtraction reverses the rounding on the subtrahend and clamps the result at zero. Mantissa products and shifted division numerators are exact in 128 bits before outward packing. The integer checker verifies that the last quota at the minimum cap is right of the central minimum and has baseline curvature greater than four. Every new interior quota at a larger cap therefore passes separation. One can also see this directly since for such a quota $`k`$, $`n-k+1\le n/10+2`$, and $`\log g_k\ge d/(n-k+1)\ge45/28>\log4`$.

[Commands and archived replay outputs](README.md#replay).
