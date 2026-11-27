# Continuous-age return at old ordered-partition roots

Write $`q_n=O_{n,j}/n!`$ for the unweighted ordered-block rows and set $`q_n=0`$ at negative indices. Let $`F_n(s)=\sum_{\ell\ge0}s^\ell q_{n-\ell}/\ell!`$. For a positive integer $`h`$ define $`G_{n,h}(s)`$ by assigning weight $`t`$ instead of $`1`$ to the terms with $`\ell\ge h`$. In this notation $`F_n`$ is the unmarked age profile. [Alexandersson’s reciprocal generating function](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Marked-moment argument](README.md)

## Exact return and failure of pointwise sign control

Choosing a first block directly yields $`G_{n,j}(1)=2q_n`$ for $`n\ge1`$, while $`G_{n,h}(0)=q_n`$ for $`h\ge1`$. Differentiation gives $`\partial_s G_{n,h}=G_{n-1,h-1}`$ for $`h\ge2`$, and $`\partial_s G_{n,1}=tF_{n-1}`$. Hence the actual positive integral return is

$$
q_{n+1}=\int_0^1G_{n,j-1}(s)\mathrm{d}s.
$$

At an old root $`\xi`$, the return integrand is $`s q_{n-1}(\xi)+O(s^2)`$ as $`s\downarrow0`$ if $`j\ge3`$. Under strict oriented interlacing of the preceding pair, $`q_{n-1}(\xi)`$ has the sign of $`q_n'(\xi)`$. The desired next sign is the opposite. This obstruction occurs on actual rows already at $`j=n=3`$. There $`q_3=2+t/6`$, the old root is $`-12`$, and the integrand is $`(3/2)s-6s^2-2s^3`$. It is positive near zero and its actual integral is $`-7/4`$.

The return also gives the exact area comparison at an old zero

$$
q_{n+1}(\xi)=\int_0^1G_{n,j}(s;\xi)\mathrm{d}s-(1-\xi)\frac{q_{n-j+1}(\xi)}{j!}.
$$

At $`n=j`$ all $`q_{j-\ell}(\xi)`$ for $`1\le\ell\le j`$ are positive constants. The identity $`G_{j,j}(1;\xi)=0`$ balances the strictly positive low powers with the negative top power. Hence $`G_{j,j}(s;\xi)>0`$ throughout $`0<s<1`$. The new row at this root is strictly negative by the exact first-band argument. Thus even an arbitrary nonnegative measure of the unshifted age slices $`G_{j,j}(s;\xi)`$ cannot recover the sign, with or without adding a multiple of the vanishing old row. When all earlier rows evaluate positively at an old first root, the same argument gives strict positivity of the unshifted profile by comparison with $`s^j`$. Controlling its signed area requires the boundary term above.

## A convolution identity for the same sign

Let $`Q(z,t)=\sum_{n\ge0}q_n(t)z^n`$, and let $`B_j`$ be the block series from the reciprocal denominator $`1-B_j`$. The original unit weights give the exact identity $`\partial_z B_j=1+B_j+(t-1)z^{j-1}/(j-1)!`$. Consequently

$$
(n+1)q_{n+1}=2[z^n]Q^2-q_n-(1-t)\frac{[z^{n-j+1}]Q^2}{(j-1)!}.
$$

At an old zero $`\xi`$ the middle term vanishes. If all strictly earlier rows evaluate positively at $`\xi`$, the two remaining coefficients of $`Q^2`$ are positive sums, and the desired first-root sign is exactly the inequality

$$
2[z^n]Q(z,\xi)^2<\frac{1-\xi}{(j-1)!}[z^{n-j+1}]Q(z,\xi)^2.
$$

This gives another explicit comparison for the newest row outside the degree-one band. The searches of Alexandersson’s block-weight issue and the independent ordered-conjecture investigation located the reciprocal and insertion recurrences, finite tests and pole methods. Alexandersson discusses a sliding window for the distinct family allowing only singleton or large blocks. Those sources supply context for the signed area comparison. [Alexandersson’s block-weight discussion](https://github.com/PerAlexandersson/RealRooted/issues/2590) · [Independent investigation](https://github.com/1337isnot1337/solved-conjectures/issues/108)
