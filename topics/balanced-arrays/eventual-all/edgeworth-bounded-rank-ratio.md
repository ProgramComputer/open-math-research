# Sparse-profile Edgeworth transfer for bounded rank ratio

Assume the following uniform sparse fixed-profile Edgeworth estimate. If an $`n\times d`$ binary array is formed by independent uniform subsets of prescribed row sizes $`s_j`$, $`\sum_j s_j=di`$, $`i/d\to\beta\in(0,\infty)`$, and $`\max_j s_j=o(d)`$, the probability of all column sums equal to $`i`$ is

$$
\sqrt d(2\pi\Lambda)^{-\nu}\exp[-1/(12\beta)+o(1)],
\quad \Lambda=\sum_j\frac{s_j(d-s_j)}{d(d-1)},\quad\nu=(d-1)/2.
$$

The uniform error is needed across all retained profiles; this note is conditional on that input.

Let $`d\to\infty`$, $`b=d^2/n\to\infty`$, and $`b=o(d)`$. At $`k/d\to\beta\in(0,\infty)`$, work at fixed feasible integer offsets $`i=k+O(1)`$. Let $`m=di/n\asymp b`$, $`H(z)=\sum_{s\le r}\binom ds z^s`$, $`A_i=[z^{di}]H(z)^n`$, and $`S`$ be the capped binomial power tilt of mean $`m`$, with variance $`V`$. At exact saturation use the deterministic row size $`r`$. Set $`\Lambda_*=i(d-m)/(d-1)`$. If $`r=O(b)`$, all profiles with total $`di`$ have $`s_j\le L=r=O(m)=o(d)`$. More generally the transfer below also holds if $`L=A(m+\log n)=o(d)`$ and both the actual balanced arrays and the scalar law conditioned on its total have $`o(1)`$ mass above this maximum row size, with the scalar unconditioned second-moment clipping error $`o(m)`$. The latter case is proved by a switch for $`r/b\to\infty`$ in [the lower-quota overlap note](edgeworth-finite-lower-overlap.md).

## Averaging the Edgeworth covariance

With $`\widehat V=n^{-1}\sum_j(s_j-m)^2`$ on profiles of total $`di`$,

$$
\Lambda=\Lambda_{\ast}\left(1-\frac{\widehat V}{m(d-m)}\right).
$$

On profiles with all rows at most $`L`$, one has $`\widehat V\le m(L-m)`$, and $`L=o(d)`$. Their covariance multiplier $`(\Lambda_*/\Lambda)^\nu`$ is thus at most $`\exp(CL)`$. The row size law under independent scalar rows conditioned on total $`di`$ has profile weights proportional to $`\prod_j\binom d{s_j}`$. Conditioning costs at most $`nr+1`$: the total size mass function is log-concave, and Jensen for its concave log interpolation at its integer mean bounds the log mass below by minus the entropy, at least $`-\log(nr+1)`$. For saturation conditioning is trivial.

We need probability errors smaller than $`e^{-CL}/(nr+1)`$. For independent rows use $`Y=(S-m)^2\mathbf1_{\{S\le L\}}/m`$, with $`Y=(S-m)^2/m`$ without clipping when $`L=r`$. The standard cap variance comparison $`V\le m(1-m/d)\le m`$ applies after every real tilt. Writing $`m(t)`$ for the mean after tilt by $`e^{tS}`$ gives $`0\le m'(t)\le m(t)`$, hence the centered log mgfs are bounded by $`m(e^{\pm t}-1\mp t)`$ for $`t\ge0`$. The upper bound follows from $`m(t)\le m e^t`$; the lower-tail bound follows from $`m(-t)\ge m e^{-t}`$. Chernoff gives

$$
\mathbb P(|S-m|\ge x)\le 2\exp[-c x^2/(m+x)].
$$

If $`m\ge\log n`$ or if $`L=r=O(m)`$, then $`L\le C m`$. On the nonzero support of $`Y`$, $`|S-m|\le C'm`$, so the last inequality gives $`\mathbb P(Y>u)\le2e^{-c' u}`$ uniformly. Thus $`Y`$ has a uniformly bounded exponential moment near zero, and the centered log mgf is $`O(t^2)`$ there by Taylor and that bound. The row average deviates from its expectation by more than $`\varepsilon=((L+\log n)/n)^{1/4}`$ with probability at most $`2e^{-c n\varepsilon^2}`$. Here $`\varepsilon\to0`$ and $`n\varepsilon^2/(L+\log n)\to\infty`$ since $`L=o(d)`$ and $`n/d\to\infty`$. If instead $`m\le\log n`$ and $`L=O(m+\log n)`$, use $`Y=O(\log^2 n)`$ because $`m\to\infty`$. Hoeffding at tolerance $`n^{-1/8}`$ yields the same required superexponential comparison with $`L+\log n`$. In either case conditioning on total and multiplying by $`\exp(CL)`$ still gives $`o(1)`$ exceptional contribution. The near-saturation deterministic law also satisfies the same bounds.

On typical retained profiles $`\widehat V=V+o(m)`$, by the clipping error assumption. There $`\widehat V=O(m)`$, and Taylor gives $`\nu\log(\Lambda_*/\Lambda)=\nu V/[m(d-m)]+o(1)`$, since the square term is $`O(d^{-1})`$. Their conditional probability tends to one. The uniform Edgeworth estimate now gives

$$
a_i=A_i\sqrt d(2\pi\Lambda_{\ast})^{-\nu}
\exp\negthinspace \left[-\frac1{12\beta}+\frac{\nu V}{m(d-m)}+o(1)\right].
$$

If clipping was used, the count of actual balanced arrays discarded is a relative $`o(1)`$ by assumption, so the formula holds for $`a_i`$ itself. The variance correction is bounded by $`1/2`$ up to a vanishing error. The auxiliary determinant term has adjacent first difference
$`-\nu(\log\Lambda_*(i+1)-\log\Lambda_*(i))=-\nu/i+o(1)`$, since $`i\asymp d`$ and $`d/n=o(1)`$. Its second difference is therefore $`o(1)`$.

## Signs when $`r=O(b)`$

Let $`D=\lfloor nr/d\rfloor`$. The [orientation inequality](https://github.com/ProgramComputer/open-math-research/blob/78e9ef2c0c0b7a5daed126efbe12a46d030d8200/topics/balanced-arrays/orientation-normalization.md) gives $`\Gamma_i=a_i^2/(a_{i-1}a_{i+1})\ge(1+1/i)^d(1+1/(n-i))^d`$, hence strictly ordered geometric nodes $`t_i=\sqrt{a_{i-1}/a_{i+1}}`$, uniform positive log curvature when $`D/d=O(1)`$, and correct sign at each $`\Gamma_i>4`$. The last implication is the elementary pairwise alternating-tail bound. Possible failing internal nodes must have $`k/d`$ bounded away from zero by orientation and bounded above by $`D/d\le r/b`$. Take a subsequence with $`k/d\to\beta>0`$ and $`V(k)/b\to v\in[0,\infty)`$.

For real quota $`x`$ use the tuned tilt with mean $`dx/n`$ and set $`E(x)=n\log H(z)-dx\log z`$, with $`E''=-b/V`$ in the interior. Then $`A_i=e^{E(i)}L_i`$, with $`L_i`$ the integer-mean lattice probability. The [log-concave lattice estimates](https://github.com/ProgramComputer/open-math-research/blob/78e9ef2c0c0b7a5daed126efbe12a46d030d8200/topics/balanced-arrays/dense-regime/rank-dependent/small-variance.md) give $`|dV/dm|\le C(1+\sqrt V)`$ and $`L_i=(2\pi nV(i))^{-1/2}(1+o(1))`$ whenever $`n\min(1,V(i))\to\infty`$. The first bound makes $`\sqrt{1+V}`$ Lipschitz; unit quota shifts change the mean by $`b/d=o(1)`$. The deficit $`J=r-S`$ is log-concave relative to the geometric law of its mean $`h=r-m`$ (its ratio to the geometric masses is log-concave), so $`V\le h(1+h)`$. This follows by subtracting the line through the two crossings of the mass difference when testing any convex function, using equal masses and means. The [modal-atom estimate](https://github.com/ProgramComputer/open-math-research/blob/04564a728c21eab6ce511b98a48ccaac754648ff/topics/balanced-arrays/very-tall/very-tall-interior-saddle.md) gives $`V\ge c\min(1,m,h)`$.

- If $`v>0`$, then $`h\gtrsim\sqrt b`$, so the upper support distance $`nh/d`$ diverges, and the lower distance is $`k\asymp d`$. At bounded offsets $`V/b\to v`$ uniformly, the lattice probabilities have relative ratios $`1+o(1)`$, and the determinant and bounded variance correction have curvature $`o(1)`$. Consequently $`\log\Gamma_{k+j}\to1/v`$ at every fixed offset.
- If $`v=0`$ and $`h\ge\eta>0`$, then $`V`$ stays bounded below at neighboring shifts. The Lipschitz bound for $`\sqrt{1+V}`$ gives relative variation $`o(1)`$ even when $`b\gg d^{1/3}`$: $`\sqrt{1+V(x)}`$ changes by $`O(b/d)=o(1)`$. Thus the lattice prefactors have log differences $`o(1)`$ and $`V=o(b)`$ uniformly across the unit neighborhood. Entropy curvature diverges, while the fixed-margin corrections are bounded, so $`\Gamma_k\to\infty`$.
- If $`h\to0`$, set $`e=nh\ge d`$ at an internal quota. The [scalar negative-binomial deficit bound](https://github.com/ProgramComputer/open-math-research/blob/04564a728c21eab6ce511b98a48ccaac754648ff/topics/balanced-arrays/very-tall/very-tall-upper-quota.md#the-last-od-quotas) gives positive log curvature of $`A_i`$ at least $`(1-o(1))b/(h+b/d)\to\infty`$, including the case with an exactly saturated neighbor. The fixed-margin formula above is valid at saturation, and its prefactor and bounded correction preserve the divergence. Thus $`\Gamma_k\to\infty`$.

In the first case, fixed-offset magnitudes normalized by the central term at $`-t_k`$ tend to $`e^{-j^2/(2v)}`$. The global orientation curvature is bounded below by a positive constant since $`D/d=O(1)`$, giving a summable Gaussian majorant. The resulting alternating theta sum is strictly positive by Gaussian Poisson summation. The divergent cases directly give correct signs. Thus every internal geometric sign is eventually correct in this regime, and the full root count consists of simple negative zeros. No assumption $`b=o(d^{1/3})`$ is used.
