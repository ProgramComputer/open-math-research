# Independent review of the comparable-threshold outer ranks

**Verdict.** The argument proves the fixed-rank conclusion, including uniformity in the remainder and the step where the degree increases. For each fixed $`C>0`$ and integer $`H\ge1`$, it applies once $`m`$ and $`j`$ are sufficiently large with $`j\le Cm`$. Both thresholds may depend on $`C,H`$. The result is partial progress on the ordered-set-partition conjecture in issue #1. It leaves the non-extreme ranks and the regime $`j/m\to\infty`$ open. [Alexandersson’s original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/1)

The source sums over every ordered partition of the label set and marks each block of size at least $`j`$. For a row with exactly $`p`$ large blocks, fixing their order leaves $`p+1`$ short-block sequences. Hence the coefficient divided by $`n!`$ is $`(j!)^{-p}[z^{n-pj}]T_j^{p+1}U_j^p`$, as claimed. Every count of large blocks from zero to $`m`$ is attainable using blocks of size $`j`$ and singletons. For $`m\ge1`$ this gives positive constant and leading coefficients for both the original and reversed rows, exact degree $`m`$, and a multiplicity-preserving inversion of their roots.

## Uniform lattice estimate

For a short-gap summand, write $`p_a`$ for its tilted mass. The identity for the square of the characteristic modulus gives

$$
1-|\phi(\theta)|^2=\sum_{a,b}p_a p_b(1-\cos((a-b)\theta))\ge2p_0p_1(1-\cos\theta).
$$

Here $`p_0=1/T_j(r)`$ and $`p_1=r/T_j(r)`$ for $`j\ge2`$. On the chosen compact radius interval, $`T_j(r)\le(2-e^r)^{-1}`$. Thus the product over $`p+1`$ short gaps is bounded by $`\exp(-c mr\theta^2)`$ for $`|\theta|\le\pi`$, uniformly as $`r\to0`$. The long-block factor can only decrease this modulus. This removes any possible competing lattice peak even when the expected excess per summand tends to zero.

The coefficientwise comparison with $`(2-e^z)^{-1}`$ and $`e^z`$ bounds every positive-order raw moment by $`O(r)`$, also at all radii reached by the small log-radius changes. The centered moments used in the Taylor expansion satisfy the same bound. The two short-gap masses give a lower bound of order $`r`$ on both the mean and the variance. For the total variable this proves $`\sigma^2\asymp mr\asymp e`$ at its saddle, and $`\mu'(r)=\sigma^2/r`$. The fixed radius $`R`$ exists since the limiting short-gap log derivative tends to infinity as $`R\uparrow\log 2`$, while $`e\le(H+2)Cm`$ for the finitely many saddle indices needed.

For clarity, Fourier inversion gives the stronger absolute estimate

$$
L_p(e+a;r)=\frac{1}{\sqrt{2\pi\sigma^2}}+O_{C,H,a}(e^{-1})
$$

for bounded integer offsets $`a`$ and growing $`e`$. Indeed each centered factor differs from one by $`O(r\theta^2)`$ for uniformly small $`\theta`$. The sum of their log expansions is $`-\sigma^2\theta^2/2+O(e|\theta|^3)`$, with the quadratic log remainders bounded by $`O(mr^2\theta^4)`$. On a sufficiently small fixed angular interval, the error in the exponential is bounded by $`O(e|\theta|^3\exp(-c e\theta^2))`$ by interpolation of the two exponents. The offset phase costs at most $`|a\theta|`$. Both errors integrate to $`O(e^{-1})`$. The remaining torus integral is exponentially small by the characteristic-function bound. Hence the relative error is $`O(e^{-1/2})`$, with constants uniform in $`e/m`$, including $`e/m\to0`$.

For bounded $`e`$, the coefficient expansion in $`p`$ is uniform because only a fixed number of Taylor coefficients of $`T_j`$ and $`\log A_j`$ occur. The leading term is $`p^e(1+1/(j+1))^e/e!`$. The ratio at adjacent indices follows at $`e=0`$ as well. For $`1\le e\le E`$, the facts $`r\asymp e/m`$ and $`\log F_p(r)=O(mr)`$ give a strictly positive lower bound on the saddle mass, with constants allowed to depend on the fixed $`E`$. Choosing $`E`$ large enough for the uniform lattice estimate yields a lower bound proportional to $`(e+1)^{-1/2}`$ for every saddle needed. The zero saddle has mass one at zero.

## Geometric tails and root ranks

The exact tilted identity is $`b_{q+1}/b_q=D(r)L_{p_{q+1}}(e_{q+1};r)/L_{p_q}(e_q;r)`$ at any positive radius. For a simultaneous comparison over an arbitrary index distance, it is preferable to divide the coefficient formulas directly so only the saddle mass and the mass at the target index remain. That direct quotient is valid all the way to $`p_q=0`$. The target mass is at most one, and no uniform variance or coefficient estimate at the target index is needed.

At the right saddle the numerator law has downward displacement at least $`j`$. At the left saddle the denominator law has upward displacement at least $`j`$. Their log-radius second derivatives are $`O(j)`$ throughout a fixed small interval about the saddle because $`mr=O(j)`$ there. Choosing the Chernoff step small gives an exponential upper bound $`e^{-cj}`$ on the displaced point masses with the stated directions. The left tail is empty at $`h=0`$, covering the only possible zero saddle. With $`q=O(\sqrt j)e^{-cj}`$ denoting either directional shrink factor, the combined noncentral contribution on $`1/2\le |z|\le2`$, divided by $`|z|^h`$, is $`O(\sqrt j\sum_{l\ge1}(2q)^l)=O(j e^{-cj})`$. This estimate sums the entire coefficient tail before taking the asymptotic. The first term of the right tail gives the exponential upper bound on $`y_h/y_{h+1}`$.

The Rouché circles of radii $`1/2`$ and $`2`$ enclose $`h`$ and $`h+1`$ zeros, counted with multiplicity, by comparison with $`z^h(1+z)`$. The shrinking circle about $`-1`$ lies in that annulus and encloses one zero counted with multiplicity. Conjugation and reality of the coefficients force that zero to be real. This gives a simple negative root with exactly $`h`$ zeros of smaller reciprocal modulus, even if other roots are complex. The proof supplies the rank $`H+1`$ used as the upper comparator in the last inequality at $`h=H-1`$.

## Direction of motion and the degree increase

With unchanged degree, raising both coefficient residuals by one multiplies $`y_h`$ by the numerator adjacent coefficient ratio divided by the denominator adjacent coefficient ratio. At the respective saddles this is $`(1+o(1))r_{h+1}/r_h`$ when $`e_h`$ grows. The sign of the ratio is in the needed direction since $`\mu_{p_h}(r_{h+1})\ge e_h+j`$ while $`\mu_{p_h}(r_h)=e_h`$. In particular $`r_{h+1}-r_h\ge j/(C_1m)`$ and $`r_{h+1}\le C_2j/m`$. If $`e_h`$ is bounded, the motion ratio is asymptotic to $`mr_{h+1}/(e_h+1)`$ and grows at least linearly in $`j`$ for each fixed bounded range. In all cases the motion ratio is uniformly bounded below by $`1+\delta`$ for some $`\delta>0`$ and above by $`O(j)`$. The latter follows from $`r_h\gg e_h/m`$ in the growing case. The exponentially small relative root errors preserve the first strict inequality, and an $`O(j)`$ change cannot cross the exponentially more distant next old rank.

At the last remainder, $`n=mj+j-1`$, the new row has degree $`m+1`$ and remainder zero. Relabeling index $`h`$ as $`h+1`$ preserves the two powers of $`A_j`$, and the new residuals are the old residuals plus one. Thus $`y_{h+1}(n+1)/y_h(n)`$ obeys the same upper and lower bounds. The extra new balance satisfies $`y_0(n+1)/y_1(n+1)\le e^{-c'j}`$, which combines with $`y_1(n+1)/y_0(n)=O(j)`$ to put the extra new root first in increasing reciprocal modulus. The other new ranks lie between successive old ranks. The map $`\rho\mapsto-1/\rho`$ is strictly increasing on positive reciprocal moduli, so the written inequalities have the correct direction on the original negative axis. They start with the old root at fixed degree and the new root at a degree increase.

Two editorial changes would make the statement easier to read. Describe $`P_{n,j}`$ explicitly as summing over all ordered partitions and marking each large block. Use SymCat’s actual anchor `#openProblemsSetPartitions`. The proof gives an asymptotic threshold and does not specify a finite numerical cutoff.

Reviewed independently with agent assistance by Codex (`lower_sign_replay`), 2026-11-26. Source reviewed at SHA-256 `8c0e846afa929eed144483e54998766ee04b9dca4f51a43368b0b85da9460d1a`.
