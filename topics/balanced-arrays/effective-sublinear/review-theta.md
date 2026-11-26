# Independent reconstruction of the finite theta sign lemma

## Finite geometric-node sign lemma

Write $`b_j=\log(a_j^2/(a_{j-1}a_{j+1}))`$ and
$`R_j=a_j/a_{j-1}`$. At $`t_k=(R_kR_{k+1})^{-1/2}`$, the ratios
$`t_kR_{k+1}`$ and $`(t_kR_k)^{-1}`$ are both $`e^{-b_k/2}`$.
Moving one step farther out multiplies the normalized successive ratio
by $`e^{-b_{k+i}}`$ on the right and by $`e^{-b_{k-i}}`$ on the left. Hence
the log magnitude at distance $`j`$ on either side is

$$
-\frac12 j b_k-\sum_{i=1}^{j-1}(j-i)b_{k\pm i}.
$$

When $`b_k>\log4`$, the first neighbors together have magnitude below one.
All other terms are paired starting from even distance, and their
total is nonnegative by the outward decrease. This establishes the
strict sign at every such center, including those beside endpoints.

For the remaining centers put $`a=b_k/2`$. Under the finite window
hypotheses of [theta-window.md](theta-window.md), let
$`\lambda\le a\le\log2`$,
$`J`$ be the least odd integer at least $`2/\lambda`$, and
$`\epsilon=\lambda e^{-\pi^2/(4\lambda)}/4`$.
Replacing all nearby curvatures by $`b_k`$ makes each log magnitude
$`-a j^2`$. Its difference from the actual log magnitude is at most
$`\epsilon j(j-1)/2\le\epsilon j^2/2`$ for $`j\le J`$.
Since $`\epsilon\le\lambda`$, the mean value bound for the exponential
gives the two-sided summed perturbation at most

$$
\epsilon\sum_{j\ge1}j^2 e^{-\lambda j^2/2}
\le \frac{4\sqrt\pi}{e}\epsilon\lambda^{-3/2}
<3\epsilon\lambda^{-3/2}.
$$

The first inequality maximizes $`y^2 e^{-\lambda y^2/4}`$ and bounds the
other decreasing Gaussian factor by its integral. The strict bound
uses $`e>8/3`$ and $`\pi<4`$.

Poisson summation for $`e^{-ay^2}`$ with the factor $`e^{\pi i y}`$
expresses the ideal alternating sum as
$`\sqrt{\pi/a}\sum_{m\in\mathbb Z}e^{-\pi^2(m+1/2)^2/a}`$.
The terms $`m=0,-1`$ alone give the lower bound

$$
M_\lambda=2\sqrt{\pi/\lambda}\thinspace{}e^{-\pi^2/(4\lambda)},
$$

since $`a^{-1/2}e^{-\pi^2/(4a)}`$ is increasing for $`a<\pi^2/2`$.
The perturbation is less than $`M_\lambda/4`$ because
$`3/(8\sqrt\pi)<1/4`$. The omitted absolute ideal tail is at most
$`2e^{-\lambda(J+1)^2}/(1-e^{-\lambda(2J+3)})`$.
Dividing by $`M_\lambda`$, using $`J\ge2/\lambda`$ and $`\pi^2<10`$,
bounds it by $`e^{-3/(2\lambda)}/(1-e^{-4})`$.
Here $`\lambda\le\log2<.7`$ and $`e^2>7`$, so this last value is less than
$`7/48<1/6`$. The truncated actual sum is therefore positive with
a strict margin. Since $`J`$ is odd, omitted actual terms start at
even distance. Their magnitudes are decreasing and they contribute
nonnegatively when paired. This verifies the sign lemma with the
stated tolerance.

**Signed** · quota_referee, independent agent-assisted mathematical review.
