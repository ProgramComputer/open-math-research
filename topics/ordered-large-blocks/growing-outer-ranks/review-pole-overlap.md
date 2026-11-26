# Independent audit of the pole overlap with a fixed real saddle

**26 November 2026 · Agent-assisted review.** I audited the contour and rank arguments in the [diverging-pole draft](moving-poles.md) with the upper condition replaced by $`u\le\varepsilon j`$ for a sufficiently small fixed positive $`\varepsilon`$. The pole analysis survives this replacement if the whole padded window has $`\inf M/u^2\to\infty`$. In particular this applies up to $`\varepsilon j`$ when $`j=o(\sqrt M)`$. Exact ranks through the pole window use the [fixed-scaled-modulus starting argument](compact-start.md). The proposed saddle join requires an exact rank count or a common bracket with exhaustion on both sides, as detailed below.

## Order of constants and the separator

Choose the compact nonvanishing disk for $`G,V_j/V_j(1)`$ first. Choose $`K`$ next, large enough for all enclosed pole coordinates, the far-angle estimate, and the two test heights $`v/u=1,10`$. Choose $`\varepsilon`$ last. The disk in the $`w`$ coordinate must accommodate $`|v|\le Ku`$ and bounded padding, so decrease $`\varepsilon`$ by a factor depending on $`K`$. On that disk

$$
 |\alpha_j(w)|\le C|w|/j,\quad
 |\alpha_j^{(a)}(w)|\le C_a j^{-a},\quad
 |\Im\alpha'_j(x+iv)|\le C|v|/j^2 .
$$

The first bound uses $`\alpha_j(0)=0`$. The final one uses reality on the real axis. In the strip $`x=u+O_K(1)`$, the main imaginary part of $`F'`$ is of order $`-v/u^2`$ with constants depending on $`K`$. The analytic correction is a small relative error once $`C_K\varepsilon^2`$ is small. The real derivative remains bounded above and below by positive constants. Thus the real-level curve, its monotonicity, the monotonicity of its target phase, and the quadratic separation of real parts hold with uniform constants.

Write $`d=u-a`$ with $`1\le a\le2`$. The proposed separator equation now has the uniform comparison

$$
 \Re F(d+iuv)-A=-a+\tfrac12\log(1+v^2)+O_K(1/u+\varepsilon)
$$

for bounded $`v`$. At $`v=1`$ and $`v=10`$ the main expressions lie strictly on opposite sides of zero for all $`a`$ in this interval. Choose the fixed lower endpoint for $`u`$ large and $`\varepsilon`$ small enough to preserve those margins. The derivative in the unscaled height is of order $`1/u`$ at the unique crossing. Hence the crossing phase varies by order $`u`$ while $`d`$ runs through the unit separator interval. The original choice avoiding the two phase classes still works.

On the near arc $`|C_j(w)|`$ stays bounded below from the compact analytic disk. On the far arc the size $`O(u/j)`$ of the long-block term is dominated by the lower bound of order $`|\theta|`$ on $`|1-z|`$ after choosing $`K`$ large. An enclosed zero satisfies $`|1-z|=O(u/j)=O(\varepsilon)`$, so the principal logarithm exists and has $`|w|\le Ku`$. This containment can use an absolute constant before choosing $`K`$, since it follows from the uniform norm of $`V_j/V_j(1)`$, not the local phase bounds. Therefore the curve accounts for all enclosed poles. For bounded targets their real parts are $`u+O(\varepsilon+u^{-2})`$, so the separator remains at least $`1/2`$ farther left.

## Errors and complex root labels

All contour inequalities in the value and contrast estimates use the sizes $`u/j`$, $`1/j`$, and $`|\theta|`$ themselves. They do not differentiate an error term merely known to be little-oh. The variation costs $`O(u^3)`$ and $`O(u)`$ in the split contrast estimate remain valid. Multiplication by the principal normalization gives $`O(e^{-cM}/j)`$, with the fixed-circle contribution bounded using $`n\ge j`$. The pole weights still satisfy

$$
 |r e^{w_b/j}-1|\le C|b|/j
$$

because $`|b|=O_K(u)`$ and $`u/j`$ is small and bounded. Their weighted Gaussian series therefore gives the desired consecutive error $`O(e^{-cM/u^2}/j)`$. For real parameters the principal pair has $`|v|\asymp1`$, so the signed principal difference is of order $`1/j`$. The estimate is adequate even if $`\mu=M/u^2`$ grows arbitrarily slowly.

For complex $`Q`$, the real-level curve is unchanged and only its target classes shift. The one-pole and two-pole exclusions use the same real-part gaps, and pointwise choices of contour are adequate because the normalized error is analytic after subtracting the two analytic principal branches. On the fixed padded log-parameter disks one has $`F''=O(u^{-2})`$ and $`\Im F'(w_+)\asymp-u^{-2}`$. Thus $`\Phi'\asymp M/u^2`$ on the real interval and the complex derivative lower bound follows as before. The Rouché argument in phase space still gives real simple roots and no extra complex roots in the annulus. Use a slightly larger padded window to count full phase bands near the upper endpoint.

The exact phase match with the compact starting window survives. In the scaled physical coordinate the original denominator derivative satisfies $`\lambda P'(\lambda z)=H(z)D'(z)`$ at the pole, so the present residue equals $`-1/(\lambda zP'(\lambda z))`$. Comparing the lower pole with the conjugate upper pole shows that the old and new phase expressions differ from the compact phase by the same odd multiple of $`\pi`$. To count by original modulus, take the start strictly within the compact real-rooted disk. A zero below the lower boundary in $`|Q|`$ has $`|q|\le |Q|+1`$, and the fixed compact padding absorbs this additive one. Within the pole annulus all zeros are on the positive real $`q`$ axis, where $`Q=1+q`$ preserves order. Thus continued band counts are genuine modulus ranks among all complex roots.

## Exact nature of the saddle join

Use the short-block pole normalization $`\rho_j`$ in the real-positive saddle, so a fixed normalized saddle radius $`r\in(0,1)`$ gives the coefficient step scale

$$
 D(r)=\frac{j!\rho_j^{-j}r^{-j}}{T(r)U(r)}.
$$

For $`r`$ in a fixed compact interval in $`(0,1)`$, and $`q=D(r)\exp(o(j))`$,

$$
 A/j=-\log r+o(1),\qquad u/j=-\log r+o(1)
$$

uniformly there. Indeed the conversion factor $`jV_j(1)`$ cancels $`j!`$ and changes the logarithm only by $`O(\log j)+j\log(\lambda/\rho_j)=o(j)`$. At the coefficient balance itself the tilted point masses of the two adjacent residuals have ratio $`1+o(1)`$: at a fixed real saddle both variances are of order $`m`$, and the shift is $`O(j)=o(\sqrt m)`$. This also follows directly from the compact-radius local Fourier argument. Thus a compact radius interval containing $`e^{-\varepsilon/2}`$ and contained strictly in $`(e^{-\varepsilon},1)`$ maps strictly inside the expanded pole window. Its length in $`A`$ is proportional to $`j`$, so its pole phase has width of order $`m/j`$ and contains many complete bands.

There is a rank-matching requirement at this seam. The asymptotic defect estimate $`m-K(A)=m/u+O(m/u^2+m/j+1)`$ has an unbounded error of order $`m/j`$ here. It can show that the windows overlap, but cannot identify matching integer ranks. If the real-saddle proof already supplies exact modulus counts, their agreement follows by identifying a common root inside the positive-width overlap. If it supplies only sign brackets, then the join needs exhaustion of the saddle annulus with no missing or extra complex roots and a common bracket or root at which to transfer the old and new counts separately. A matching coarse phase asymptotic alone would leave the relative rank shift unproved. I found no contour or precision obstruction on the pole side.
