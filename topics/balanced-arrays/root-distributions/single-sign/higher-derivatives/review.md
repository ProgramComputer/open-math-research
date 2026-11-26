# Independent review of all-order geometric-circle counts

Agent-assisted mathematical review by Codex (`edge_referee`), 2026-11-26.

I accept the derivative theorem at the sharp closed threshold $`Q_m=[2(m+1)]^{2/(2m+1)}`$. I also obtain the open and closed disk-count bounds at this same closed threshold. Sharpness here is established for the derivative threshold. The disk-count threshold may be smaller.

## Alternating Taylor coefficients

Let $`P(z)=\sum_{i=0}^D a_i z^i`$ have positive coefficients and $`G_i=a_i^2/(a_{i-1}a_{i+1})\ge Q_m`$ at every internal index. Fix an internal $`k`$, its radius $`v=\sqrt{a_{k-1}/a_{k+1}}`$, and let $`A(x)=1+\sum_{j=1}^J c_jT_j(x)`$ be the real part of $`P(vz)/(a_k(vz)^k)`$ on $`z=e^{i\theta}`$, $`x=\cos\theta`$, with $`J=\max(k,D-k)`$. Here $`c_j>0`$ for $`1\le j\le J`$, and zeros may pad the tails past their endpoints. Each outward ratio after distance $`j`$ is at most $`Q_m^{-j-1/2}`$. Summing the two corresponding coefficient inequalities gives $`c_{j+1}\le Q_m^{-j-1/2}c_j`$.

For integers $`N\ge j\ge1`$, the identities needed at the endpoints are

$$
T_N^{(j)}(1)=N,2^{j-1}(j-1)!\binom{N+j-1}{N-j},
\qquad
T_N^{(j)}(-1)=(-1)^{N-j}T_N^{(j)}(1).
$$

The parity follows from $`T_N(-x)=(-1)^NT_N(x)`$. Differentiating the Chebyshev differential equation $`j-1`$ times at $`x=1`$ gives $`T_N^{(j)}(1)=[N^2-(j-1)^2]T_N^{(j-1)}(1)/(2j-1)`$. Multiplying these recurrence factors gives the stated value. Equivalently it follows from the first Chebyshev derivative and the ultraspherical derivative identity. [NIST DLMF §18.9(iii)](https://dlmf.nist.gov/18.9.iii)

For any $`j\ge m`$ with $`c_j>0`$, set $`u_\ell=c_{j+\ell}T_{j+\ell}^{(j)}(1)`$. Then $`A^{(j)}(-1)=\sum_\ell(-1)^\ell u_\ell`$. Whenever the consecutive terms are present,

$$
\frac{u_{\ell+1}}{u_\ell}
\le
\frac{j+\ell+1}{j+\ell}\frac{2j+\ell}{\ell+1}
Q_m^{-j-\ell-1/2}
\le 2(j+1)Q_m^{-j-1/2}.
$$

The factors in the middle product decrease with $`\ell`$, and the last expression decreases with $`j\ge m`$, since $`Q_m>1+1/(m+1)`$. The latter follows from $`\log Q_m>2/(2m+1)>1/(m+1)>\log(1+1/(m+1))`$. At $`j=m`$ and $`\ell=0`$ the bound is exactly one. All later ratios are strictly below one. The alternating sums are therefore nonnegative. The only possible zero with $`m\le j\le J`$ is at $`j=m`$, $`J=m+1`$, with $`u_1=u_0`$. When all $`G_i>Q_m`$, the initial ratio is also strict and all these alternating sums are positive. Taylor expansion at $`-1`$ now gives $`A^{(m)}(x)>0`$ on $`(-1,1)`$ whenever $`J\ge m`$, and on $`[-1,1]`$ outside the stated endpoint exception. For $`J<m`$ the derivative vanishes identically and the projection has degree less than $`m`$.

For sharpness, fix $`1<Q<Q_m`$ and take the middle index $`k=m+1`$ of the symmetric degree-$`2m+2`$ polynomial with coefficients $`a_{k+j}=Q^{-j^2/2}`$ for $`-m-1\le j\le m+1`$. Its radius is one, all its second quotients equal $`Q`$, and

$$
\frac{A^{(m)}(x)}{c_mT_m^{(m)}(1)}
=1+2(m+1)Q^{-m-1/2}x .
$$

This is negative just to the right of $`-1`$. The same example at threshold has normalized derivative $`1+x`$, attaining the possible endpoint degeneracy.

I also checked the earlier Laplace proof. The normalized Gegenbauer moment identity follows by expanding $`\mathrm{E}(1-t(x+i\sqrt{1-x^2}S))^{-2m}`$ using $`\mathrm{E}S^{2p}=(1/2)_p/(m+1/2)_p`$. Summing gives $`(1-2xt+t^2)^{-m}`$. For the cosine step, the null sequence $`(2b_0,b_1,b_2,\ldots)`$ is convex when $`b_1\le b_0`$ and all later successive ratios are at most $`1/2`$. Its cosine polynomial is a nonnegative combination of Fejér kernels. The real part of the associated analytic polynomial is then strictly positive in the open disk by its positive constant term. The alternating Taylor proof also yields the endpoint information needed for the next step.

## Winding and the closed threshold

For $`R>0`$, replace $`v`$ by $`R`$ while keeping the index $`k`$ fixed. Write $`F_R(z)=P(Rz)/(a_k(Rz)^k)`$ and $`A_R(\cos\theta)=\mathrm{Re}F_R(e^{i\theta})`$. The polynomial coefficients of $`A_R`$ vary continuously with $`R`$, with degree $`J`$ fixed and $`A_R(1)>0`$.

If the circle is root-free, choose a continuous upper-semicircle argument $`\alpha(\theta)`$ of $`F_R(e^{i\theta})`$ starting at $`0`$. It ends at $`W\pi`$ for an integer $`W`$, since $`F_R(-1)`$ is real. Conjugation extends the lift to the lower semicircle with final argument $`2W\pi`$, so $`W`$ is the full winding of $`F_R`$. If $`W\ne0`$, the upper argument attains the $`|W|`$ distinct half-integer multiples of $`\pi`$ between $`0`$ and $`W\pi`$. Each is a distinct zero of $`A_R`$ in $`(-1,1)`$. Consequently any root-free circle with at most $`m`$ such projection zeros has $`k+W`$ roots in its disk with $`|W|\le m`$.

At $`R=v`$, Rolle's theorem gives the projection bound. It persists at all sufficiently close radii if $`A^{(m)}`$ is positive on $`[-1,1]`$, by uniform continuity. It also persists if $`J\le m`$, by degree. In the only remaining case $`J=m+1`$ and $`A^{(m)}(-1)=0`$, suppose some sequence $`R\to v`$ yielded $`m+1`$ distinct projection zeros in $`(-1,1)`$. The projection degree and nonzero leading term persist. Taking a convergent subsequence of the ordered zeros and passing to the product of linear factors would put all $`J`$ zeros of $`A_v`$ in $`[-1,1]`$, with multiplicity. Their mean equals the sole zero $`-1`$ of $`A_v^{(m)}`$. Therefore all $`J`$ zeros would equal $`-1`$, so $`A_v=C(1+x)^J`$.

That shape is impossible. Its Chebyshev expansion, when the coefficient of $`T_0`$ is one, has $`c_1=2J/(J+1)`$, by the binomial expansion of $`(1+\cos\theta)^J`$. The outward bound instead gives $`c_1\le 2Q_m^{-1/2}<2J/(J+1)`$. The final strict comparison is equivalent to $`2J>(1+1/J)^{2J-1}`$. For $`J=2,3`$ it follows from $`4>27/8`$ and $`6>1024/243`$. For $`J\ge4`$, use $`(2J-1)\log(1+1/J)<2<\log 8\le\log(2J)`$. This excludes the hypothetical sequence and supplies a full punctured neighborhood of the original radius with at most $`m`$ open projection zeros.

Choose root-free radii close enough on either side of $`v`$ that no other root modulus intervenes. The corresponding counts are $`N_{<}(v)`$ and $`N_{\le}(v)`$, including multiplicity. Thus, also at $`G_i\ge Q_m`$,

$$
k-m\le N_{<}(v)\le N_{\le}(v)\le k+m.
$$

In particular, boundary zeros have total multiplicity at most $`2m`$. The boundary-free argument also gives $`|N_{<}(R)-k|\le Z_R`$ for any count $`Z_R`$ of distinct upper-semicircle projection zeros, without a sign-change assumption.

## Annuli and scope

The geometric radii are strictly increasing since $`v_{k+1}/v_k=\sqrt{G_kG_{k+1}}>1`$. For internal $`i<j`$, subtraction gives at least $`\max(0,j-i-2m)`$ and at most $`j-i+2m`$ roots in $`v_i<|z|<v_j`$. The same bounds hold for the closed annulus. If $`\rho_\ell`$ is the $`\ell`$th root modulus in increasing order with multiplicity, then $`v_{\ell-m-1}<\rho_\ell<v_{\ell+m}`$ when both indices exist.

For balanced arrays the orientation bound $`\log G_i>4d/(n+2)`$ supplies the hypothesis for every internal index when $`4d/(n+2)\ge 2\log(2(m+1))/(2m+1)`$. This controls locations in modulus. It gives no simplicity or reality guarantee for individual roots in these annuli. A universal disk-count threshold cannot be below $`(1+1/(m+1))^2`$, since $`(1+z)^{2m+2}`$ has this minimum second quotient and gives errors of $`m+1`$ in both counts at its middle circle. The sharp derivative threshold is distinct from that necessary disk threshold.
