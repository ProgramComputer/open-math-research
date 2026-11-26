# Independent review of the ordered-partition theta transition

**Verdict.** The argument proves the stated simple negative roots, strict consecutive order in both degree patterns, and limiting ratio of adjacent moduli under $`j/\sigma\to a\in(0,\infty)`$. The ranks are zero-based in the reversed row and count all complex roots with multiplicity. I found no mathematical gap. This is a partial theorem for the ordered-set-partition statistic in issue #1. [Alexandersson’s statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/1)

## Original coefficient and local estimates

For $`p`$ large blocks the exponential generating function contributes the product of $`p`$ marked block weights and $`p+1`$ ordered sequences of short blocks. Under the rescaling by $`\rho`$, removing $`pj`$ forced labels in the powers of the generating variable gives exactly $`(j!)^{-p}\rho^{-e}[z^e]T^{p+1}U^p`$. Every block count from zero to $`m`$ is attainable, so the original and reversed polynomials have degree $`m`$ with positive constant and leading coefficients.

For either single variable, the generating function has a pole at 1 with positive bounded residue coefficient and a uniformly analytic remainder on a larger disk. Thus its unnormalized coefficients are $`c_j+O(R^{-i})`$ uniformly. All finite coefficients are positive and uniformly bounded below, for example by the contribution from singletons in $`T`$. The tilted law is bounded above and below by constant multiples of the geometric law. This proves the stated mean, variance and third moment estimates throughout $`0<r<1`$. At the old anchor, $`mr\to\infty`$ since either $`r`$ stays away from zero or $`e_h\asymp mr`$ and $`e_h\to\infty`$.

For the mass difference Fourier inversion inserts $`e^{-i\theta}-1`$ because the target changes from $`x`$ to $`x+1`$. After multiplying by the standard deviation on top of the usual local limit normalization, the multiplier tends to $`-iv`$ in the centered scaled Fourier variable $`v`$. Integrating it against $`e^{-v^2/2-ivu}`$ differentiates the Gaussian density and gives $`-u\phi(u)`$, with the sign used in the proof.

The inner angular bound for the product is Gaussian since the denominator in the single-law modulus identity is at most $`C_M(1-r)^2`$ there. For the outer arc, put $`d=1-r`$ and choose the fixed cutoff $`M>2C`$. Direct integration of $`(Cd/|\theta|)^{p+1}|\theta|^b`$, for $`b=0,1`$ and $`p\ge3`$, gives

$$
\int_{M d}^{\pi}(Cd)^{p+1}\theta^{b-p-1}\mathrm{d}\theta=O(d^{b+1}2^{-p}).
$$

Multiplication by $`\sigma_p^{b+1}`$ gives $`O((p+1)^{(b+1)/2}2^{-p})`$ when $`r\to1`$. This verifies the integrable tails of both local limits without any restriction on how quickly $`1-r`$ tends to zero. The same inequalities before rescaling give the all-target bounds for $`p\ge3`$.

## Endpoints, carry and the two Laurent series

If $`r\to1`$ and $`p=1,2`$, a single tilted law has first-difference $`\ell^1`$ norm $`O(1-r)`$ by decomposing its coefficients into the pole contribution and the uniformly summable remainder. The difference includes the jump at the left support edge. Convolution with one other bounded law of supremum norm $`O(1-r)`$ gives the required first-difference bound. At $`p=0`$ only the actual rightmost target $`e_m=n`$ is used. Dividing the difference of $`r^{e_m+1}(c_j+O(R^{-e_m-1}))`$ and $`r^{e_m}(c_j+O(R^{-e_m}))`$ by the normalization gives $`O((1-r)^2+(1-r)R^{-e_m})`$. For the original tilt and each fixed recentered tilt near one, $`1-r\gg1/j`$ follows from the mean lower bound and the saddle target at most $`mj`$. The exponential term is therefore harmless uniformly, even when $`j`$ is superexponential in $`m`$.

At a carry the coefficient with old index $`t`$ and new index $`t+1`$ uses the same $`p=m-t`$ and excess $`e_t+1`$. At $`t=-1`$, the old mass at $`e_{-1}=-1`$ is zero and the new mass at zero is $`1/F_{m+1}(r)`$. The proposed contrast gives exactly the extra Laurent coefficient $`(\rho r)(j!)^{-(m+1)}`$ at $`y^{-1}`$. The rightmost degree $`t=m`$ continues to use the single short-gap variable, so it is covered by the preceding special bound.

Changing the tilt to $`r_b`$ gives the exact contrast numerator $`(r/r_b)\Delta L_{p_t,r_b}(e_t)+(r/r_b-1)L_{p_t,r_b}(e_t)`$ times $`\omega_t(r_b)`$. The factor $`r/r_b`$ comes from the $`\rho r`$ multiplying the new coefficient, whose excess is one greater. For fixed $`b`$ the mean shift is $`b(j+\mu_V)`$ and the variance changes by $`o(\sigma^2)`$ across the proposed log-radius interval, by the third cumulant bound. This yields $`\sigma\log(r_b/r)\to ab`$. The ratio of local masses at $`-ab`$ and $`a(1-b)`$ has limit $`\exp(a^2(1-2b)/2)`$, giving the two opposite choices of geometric tilt on the two tails.

The scaled absolute contrast bound at the new tilt costs at most a constant times $`1+m/(p_t+1)`$ after division by the anchored mass. For $`\ell=t-h\le m/2`$, the denominator $`p_t+1`$ is comparable to $`m`$, while for $`\ell>m/2`$ the factor is $`O(1+\ell)`$. The same majorant applies to the row itself. Hence the geometric factor controls all indices on each compact annulus, including the extra carried term and the $`p=0`$ term. The two compact-uniform limits are valid and their signs agree with Fourier inversion.

## Actual ranks and consecutive orientation

In the triple product only $`1+z`$ vanishes at $`z=-1`$ and every remaining factor has positive value there. Thus $`\Theta_q'(-1)>0`$. The winding numbers on $`|z|=q^{1/2}`$ and $`|z|=q^{-1/2}`$ are zero and one because only $`1+z`$ gains winding between them. Uniform convergence verifies the same winding for the Laurent normalization on both circles and produces one simple zero near $`-1`$. Restoring the removed power adds $`h`$ to both counts. This proves the actual modulus rank $`h`$ in the old row, regardless of the location of complex roots elsewhere. Taking adjacent coefficients in the limit gives $`y_h/y_{h+1}\to q`$ and repeating at fixed shifts gives the neighboring modulus ratios. [Jacobi’s triple product, DLMF 20.5.9](https://dlmf.nist.gov/20.5.E9)

At the old root, the signed contrast tends to the positive number $`a\Theta_q'(-1)`$. The original factors outside the contrast give the new value sign $`(-1)^{h+I}`$. The new balance at $`h+I`$ has ratio tending to one with the old balance, so the old root lies strictly inside the same annulus used for the new root count. The smaller new circle contains $`h+I`$ zeros. The number of negative real zeros there has the same parity because the remaining zeros occur in conjugate pairs and the row has positive coefficients. The new value therefore has the sign on the side of its unique annular zero toward zero. The previous new rank has smaller modulus by the limiting ratio $`q<1`$. This proves both orders with the stated zero-based convention.

In the very-large-threshold regime, the stated saddle condition describes the critical scale explicitly. If $`e_h/m\to\infty`$, then $`r\to1`$. Analytic numerator logarithmic derivatives in $`T,V`$ give single-law mean $`r/(1-r)+O(1)`$ and variance $`r/(1-r)^2+O(1)`$. Hence $`\sigma\sim e_h/\sqrt m\sim jh/\sqrt m`$ and $`j/\sigma\sim\sqrt m/h`$. Thus $`h/\sqrt m\to c\in(0,\infty)`$ yields $`a=1/c`$ under the proposed threshold growth. This inclusion can be stated directly in a combined theorem. In the proof text, fix the spelling of “completness” and explicitly name rank zero as the smallest reversed modulus.

Reviewed independently with agent assistance by Codex (`lower_sign_replay`), 2026-11-26. Source reviewed at SHA-256 `b955cb06e6860e3109560fb8f3a171f72e2884f6c03ac3485c6adcbc36ef2e9a`.
