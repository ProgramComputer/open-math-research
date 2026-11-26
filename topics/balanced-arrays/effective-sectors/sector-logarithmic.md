# An explicit sublinear dimension bound near full rank

**Theorem.** Let $`L=\log n\ge64`$, $`d\ge4n/L`$, $`d\ge2`$, and $`4n(d-r)\le d^2`$. Then the balanced-array polynomial has exactly $`\lfloor nr/d\rfloor`$ simple negative roots. In particular the dimension-to-height ratio may tend to zero. The earlier all-cap theorem at this scale has unspecified constants. The present cap restriction gives an effective uniform bound.

Use $`g_k,G_k,w_j`$ and the alternating-node test in the [sector proof](sector-proof.md). We may assume $`d<n`$, and put $`c=d/n`$. A quota requiring attention has $`g_k\le4`$. Necessarily $`d/2<k<n-d/2`$: otherwise $`\log g_k\ge d/(d/2+1)>\log4`$ since $`d\ge5`$. Put $`a=(\log g_k)/2`$. Then $`3c/2\le a\le\log 2`$, by $`\log g_k\ge4d/(n+2)`$.

Poisson summation for the Gaussian at frequency $`1/2`$ yields

$$
\sum_{j\in\mathbb Z}(-1)^j e^{-a j^2}
=\sqrt{\pi/a}\sum_{m\in\mathbb Z}e^{-\pi^2(m+1/2)^2/a}
\ge2e^{-2/c}.
$$

For the inequality retain $`m=0,-1`$, use $`\pi^2<12`$ and $`\sqrt{\pi/a}>1`$. Equivalently, the displayed identity follows by evaluating at $`1/2`$ the Fourier series of the periodized Gaussian of parameter $`\pi^2/a`$. [Theta transformation, DLMF 20.7.33](https://dlmf.nist.gov/20.7.E33)

Let $`J`$ be the smallest odd integer at least $`4/c`$. Then $`J\le6/c\le3L/2`$ and $`J+1\le2L\le d/8`$. The numerical inequalities used here and below follow from

$$
2e^L>5L^4, \qquad e^{L/2}>254 L^5 \qquad(L\ge64).
$$

Both ratios increase on this interval and the left-end comparisons follow from the exponential Taylor series. In particular $`e^L>4L^2`$, as needed for the window bound. Every local quota through $`k\pm(J+1)`$ is in the support and has density at most $`1-3c/8`$. The cap fraction is at least $`1-c/4`$. The binomial second-derivative estimate and union bound from the sector proof give

$$
1-p_i\le n e^{-n c^3/32}\le n e^{-2n/L^3}\le n^{-4}
$$

throughout the window. There each of the two coordinates $`i,n-i`$ is at least $`d/4`$. The derivative of the baseline log curvature in the quota has magnitude at most $`32/d`$. Thus $`|\log G_i-\log g_k|\le32J/d+4n^{-4}\le33J/d`$ for $`|i-k|\le J`$. As in the sector proof, $`|\log w_j+a j^2|\le z=33 J^3/(2d)`$ for $`|j|\le J`$.

The bound $`(2J+1)2z\le99J^4/d\le127L^5/n< n^{-1/2}/2`$ implies $`z<1`$ and bounds the sum of the absolute errors on the window, because $`e^z-1\le2z`$. The ideal Gaussian tails have absolute sum at most

$$
\frac{2 e^{-a(J+1)^2}}{1-e^{-a(2J+3)}}\le \frac{2e^{-24/c}}{1-e^{-12}}< e^{-2/c}.
$$

Therefore the actual alternating sum on the window is positive, since $`e^{-2/c}\ge n^{-1/2}`$. The rest of the actual alternating sum is nonnegative by pairing outwards from the even distance $`J+1`$ on each side. All required signs follow.

At the opposite endpoint, $`4nr\le d^2`$ gives $`D\le d/4`$, for which ordinary separation alone suffices. Both bounds leave the central caps open.
