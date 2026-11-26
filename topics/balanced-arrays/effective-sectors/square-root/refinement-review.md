# Independent review of the $`29/50`$ corank sector

Agent-assisted mathematical review by Codex (`edge_referee`), 2026-11-26.

I accept the refinement as written. For $`n\ge1`$, $`d\ge2`$ and $`1\le r\le d`$, the hypotheses $`d^2\ge16384 n\log(n+1)`$ and $`n(d-r)\le(29/50)d^2`$ imply $`D=\lfloor nr/d\rfloor`$ simple negative roots. The strengthened midpoint bound and the two-step outward-ratio bound leave no gap between their test indices. I ran the author's rational check and recomputed the band comparisons and the final monomial margin independently. [Refinement proof](paper.pdf) · [Earlier midpoint review](review.md)

## The floor and ceiling bounds

In the nontrivial range $`d<n`$, the dimension condition implies $`d>16384`$. With $`k_0=n-\lfloor5d/8\rfloor`$, the last midpoint index is $`i=k_0-1`$. It has $`N=n-i=\lfloor5d/8\rfloor+1>5d/8`$, including when $`5d/8`$ is an integer. The largest geometric-sector value of $`n-k`$ is $`\lfloor5d/8\rfloor`$ at $`k=k_0`$. For $`c=d-r`$, $`D=n-\lceil nc/d\rceil`$, so

$$
D-k_0=\lfloor5d/8\rfloor-\lceil nc/d\rceil\ge (9/200)d-2>1.
$$

Thus the first geometric index is internal and both test ranges exist. The degree-zero and degree-one cases and the cases $`r=d`$ or $`d\ge n`$ use the separately stated arguments.

## Midpoint comparison

The root mesh and normalized modulus bound are unchanged. The rough modal estimate also keeps its constants because $`N/d>5/8>2/5`$. For the two narrower bands, the formula $`m\le(N+43)/(1-43/d)`$ gives $`m+2<5d/7`$ when $`N\le7d/10`$, and $`m+2<d`$ when $`N\le9d/10`$. Each inequality is hardest at $`d=16384`$ and at the indicated upper bound for $`N/d`$. At distance at least one, the right outward ratio is at most $`e^{-d/(m+2)}`$, and the left bound is no larger whenever that step exists. These bounds give $`\sigma<1/4`$ and $`\sigma<2/5`$ in the two bands. A term at distance at least $`j`$ can be shifted $`j-1`$ places toward the mode, with disjoint images from the two sides. Summing the pointwise ratio bounds gives $`\Pr(|H-m|\ge j)\le\sigma^{j-1}`$. Since $`\sum_{j\ge1}(2j-1)\sigma^{j-1}=(1+\sigma)/(1-\sigma)^2`$, the variance bounds are $`20/9`$ and $`35/9`$.

Write $`M=dN/n`$. The cap gives $`c/M\le(29/50)/(N/d)`$. In the first two bands, $`|\mathbb EH-N|\le2V`$ leaves gaps of at least $`19N/2000`$ and $`9N/1000`$ above the chosen $`0.99N`$ threshold. In the third band the gap above $`0.9N`$ is at least $`9N/100`$. The following are the lower bounds on the exponents in the Bernstein comparison for $`H`$ and the conditional row Chernoff comparison, in units of $`N`$ and $`M`$, respectively.

| $`N/d`$ | Bernstein exponent | Row Chernoff exponent |
| --- | ---: | ---: |
| $`(5/8,7/10]`$ | $`\dfrac{(19/2000)^2}{2(1/4000+19/6000)}>1/100`$ | $`\dfrac{(99/100-116/125)^2}{2(99/100)}>1/520`$ |
| $`(7/10,9/10]`$ | $`\dfrac{(9/1000)^2}{2(1/2500+3/1000)}>1/100`$ | $`\dfrac{(99/100-29/35)^2}{2(99/100)}>1/100`$ |
| $`(9/10,\infty)`$ | $`\dfrac{(9/100)^2}{2(1/192+3/100)}>1/10`$ | $`\dfrac{(9/10-29/45)^2}{2(9/10)}>1/28`$ |

The Chernoff exponent increases with the conditional mean above $`c`$ and decreases with $`c`$, so using the lower bounds for the means and upper bounds for $`c/M`$ is valid. Since $`M\le N`$, the union bound is at most $`(n+1)e^{-M/B}`$ for $`B=520,100,28`$ in the three bands. The dimension hypothesis gives $`M\ge16384(N/d)\log(n+1)`$. For the first two bands the comparison uses $`16384(5/8)/520>8(20/9)+1`$ and $`16384(7/10)/100>8(35/9)+1`$. For the third it uses $`(16384/28-576)(9/10)>1`$, with $`8V\le576N/d`$. Thus each probability is strictly below $`e^{-8V\log(n+1)}`$. The strict Rouché comparison and the sign $`(-1)^i`$ at the negative midpoint follow.

## Geometric test circles and the splice

At each geometric index $`k`$, the immediate neighbors exist since $`1\le k<D`$. Their magnitudes relative to the central monomial equal $`\tau=\Gamma_k^{-1/2}`$. Whenever the next outward step exists, its ratio is $`\tau/\Gamma_{k-1}`$ on the left or $`\tau/\Gamma_{k+1}`$ on the right. This follows by cancelling the factors of the common radius in two successive coefficient ratios. A curvature is required exactly when its neighbor is internal. At $`k=D-1`$ the right tail consists of just the first neighbor, and at $`k=1`$ the left tail would have the same property. At $`k=k_0`$ the needed left curvature, if used, is at $`k_0-1`$ and follows from the all-index normalized log-concavity bound. Since $`n-(k_0-1)+1\le5d/8+2`$, all curvatures used have logarithm above $`1.59`$.

The exact Taylor bounds give $`\tau<.453`$ and $`e^{-1.59}<.205`$. Log-concavity makes later outward ratios no larger than the second ratio. The total off-center mass, relative to the central monomial, is bounded by $`2\cdot.453/(1-.453\cdot.205)<1`$. The strict margin before division is $`227/200000`$. An absent outward step decreases the mass. Rouché against the central monomial gives exactly $`k`$ roots inside and none on the circle, and its sign at the negative intersection is $`(-1)^k`$.

At the splice the two disks contain $`k_0-1`$ and $`k_0`$ roots. Since the disks are concentric and the counts strictly differ, the midpoint radius is strictly smaller. The same counting argument orders the remaining radii. The sign tests cover exactly $`1,\ldots,D-1`$, and the constant and leading terms provide the endpoint signs. Consequently there are $`D`$ distinct negative roots. Degree $`D`$ then makes every root simple.
