# Recursive saturation bounds at growing headroom

Independent mathematical argument and review by Codex (`edge_referee`), 2026-11-26.

Fix compact intervals $`0<\beta_-\le d/n\le\beta_+<\infty`$ and $`\delta\le k/n\le1-\delta`$ with $`\delta>0`$. Write $`T=r-dk/n`$. If $`T/\sqrt d\to\infty`$, the original capped polynomial eventually has positive normalized negative-ray sign at its index-$`k`$ geometric circle, exactly $`k`$ roots in that open disk and no boundary roots. The same conclusion holds uniformly for all sufficiently large sizes and all $`T\ge Z\sqrt d`$, for a sufficiently large fixed $`Z`$ depending only on the two compact intervals. No absolute lower bound for the cap probability is used. Full cap has no cap correction, and the proof below concerns proper caps.

## Exact recursion

For a balanced fiber with $`N`$ rows and quota $`K`$, let $`p=K/N`$, let $`e(N,K)`$ be the fraction of unavailable rows among the zeros in any one column in expectation, and set $`L(N,K)=-\log(1-e(N,K))`$. Equivalently $`e`$ is the saturation probability conditional on a specified row having zero in that column, so

$$
e(N,K)=\alpha(p)\Pr(\text{marked row has size }r),\qquad
\alpha(p)=\frac{1-r/d}{1-p}.
$$

The normalized extension ratio is $`1-e(N,K)`$ by the one-column insertion and deletion count. The known orientation comparison implies that $`L(N,K)`$ increases with $`K`$ at fixed $`N`$. When a diagonal step from quota $`K-1`$ to $`K`$ has positive endpoints, its log cap-probability decrement is between $`dL(N,K-1)`$ and $`dL(N,K)`$, provided these bounds are finite. This holds by applying the orientation comparison to each coordinate extension on the diagonal path. [Orientation comparison](https://github.com/ProgramComputer/open-math-research/blob/14a7c082563830be7b42e5353c2269944a4260b5/topics/balanced-arrays/orientation-normalization.md)

Prescribe a marked-row mask of size $`j`$ in the $`N`$-row fiber and let $`F_j`$ count its completions. The ratio from $`F_{j-1}`$ to $`F_j`$ is the inverse of a column extension at $`N-1`$ rows, between quotas $`K-1`$ and $`K`$ in one coordinate. Its binomial contribution is $`K/(N-K)`$, and its normalized correction is $`1/(1-e_{\mathrm{res}})`$. Thus

$$
F_j/F_{j-1}=(K/(N-K))\exp(L_{\mathrm{res}}).
$$

The residual base lies between the balanced bases $`K-1`$ and $`K`$ at height $`N-1`$. Therefore $`L(N-1,K-1)\le L_{\mathrm{res}}\le L(N-1,K)`$. The marked-row law has masses proportional to $`\binom d j F_j`$. Its likelihood ratios place it between two truncated binomials whose log odds are $`\log(p/(1-p))+L(N-1,K-1)`$ and $`\log(p/(1-p))+L(N-1,K)`$. In particular its top mass lies between their top masses. Define $`q_r(\zeta)=\Pr(\mathrm{Bin}(d,\zeta)=r\mid\mathrm{Bin}(d,\zeta)\le r)`$ and let $`\zeta(p,y)`$ have log odds $`\log(p/(1-p))+y`$. Then for

$$
\Psi_p(y)=-\log(1-\alpha(p)q_r(\zeta(p,y)))
$$

the exact bounds are

$$
\Psi_p(L(N-1,K-1))\le L(N,K)\le\Psi_p(L(N-1,K)).
$$

All quantities used below lie at quotas so far below the cap that these residual fibers and an additional coordinate increment are feasible. This makes every likelihood ratio in the comparison well-defined.

## Bounds on the recursion and its derivatives

Follow the recursion from quotas a fixed bounded distance from $`k`$ for $`h=\lceil4\log n\rceil`$ generations. At depth $`j\le h`$, the height is $`n-j`$ and the quota differs from $`k`$ by at most $`h+O(1)`$. Hence the density differs from $`k/n`$ by $`O(h/n)`$ and the headroom differs from $`T`$ by $`O(h)`$, uniformly. As $`T/\sqrt d\to\infty`$ and $`d\asymp n`$, all these headrooms are comparable with $`T`$ and the residual feasibility conditions hold. The constants in this section depend only on the two compact intervals and the fixed finite quota offsets.

Let $`z=T/\sqrt d`$. If a binomial parameter $`\zeta`$ differs from one of the densities in this rectangle by $`O(1/\sqrt d)`$, its headroom is still comparable with $`T`$. Its truncated top mass obeys

$$
q_r(\zeta)\le C d^{-1/2}e^{-c z^2}.
$$

For caps bounded away from the upper endpoint, apply the binomial Stirling bound with prefactor $`C/\sqrt d`$ and divergence bounded below by $`2(r/d-\zeta)^2`$. This divergence inequality follows by differentiating twice in its first argument. For caps close to the upper endpoint the gap from the compact density is a fixed positive fraction of the dimension, and the binomial Chernoff bound absorbs the missing $`d^{-1/2}`$ into a smaller exponential constant. In both cases the truncation probability is at least $`1-e^{-c z^2}`$ by the same tail bound.

At any intermediate density $`p`$, the mean of the truncated binomial at $`\zeta=p+1/\sqrt d`$ is $`d\zeta-\zeta(d-r)q_r(\zeta)`$. The second term is $`O(\sqrt d e^{-c z^2})=o(\sqrt d)`$. Hence the binomial tilt with conditional mean exactly $`dp`$ has parameter at most $`p+1/\sqrt d`$. The previously reviewed same-mean saturation comparison now gives the uniform estimate

$$
0\le L(N,K)\le Y_n=C' d^{-1/2}e^{-c z^2}.
$$

Over the whole density rectangle and $`0\le y\le Y_n`$, the shifted probability $`\zeta(p,y)`$ differs from $`p`$ by $`O(1/\sqrt d)`$, so the top mass bound applies. Its logarithmic derivative in the odds is the deficit mean $`r-\mu_\zeta`$, at most $`C T`$ by the exact truncated-mean formula. Also $`\alpha`$ and its derivative are bounded, the derivative of $`\log(p/(1-p))`$ stays bounded, and $`1-\alpha q_r`$ stays above $`1/2`$. Consequently both partial derivatives of $`\Psi`$ are bounded in absolute value by

$$
\eta_n=C''(1+z)e^{-c' z^2}\longrightarrow0.
$$

The derivatives are nonnegative, since $`\alpha`$ increases with $`p`$ and the top mass increases with log odds.

## From recursion to flat centered correction

Fix integers $`a<b`$. At generation $`j`$, compare the upper quota $`k+b`$ and the lower quota $`k+a-j`$ at height $`n-j`$. Let $`\Delta_j`$ be the difference of their $`L`$ values, nonnegative by orientation. The exact recursion and the Lipschitz bounds give

$$
\Delta_j\le \eta_n\Delta_{j+1}
+\eta_n\frac{b-a+j}{n-j}.
$$

Indeed the upper bound takes the upper residual quota unchanged and the lower bound reduces the lower residual quota by one. The change in the density argument of $`\Psi`$ is exactly $`(b-a+j)/(n-j)`$ at that generation. For large $`n`$ we can use $`\eta_n\le1/2`$. Iteration then gives $`\Delta_0=O(\eta_n/n)+o(n^{-1})`$. The weighted sum of the numbers $`b-a+j`$ is bounded by a constant depending only on $`b-a`$. The terminal contribution is at most $`2^{-h}Y_n=o(n^{-1})`$. Thus for every fixed finite neighborhood of $`k`$ the log decrements of the actual diagonal cap probabilities differ from one another by $`o(1)`$, by the diagonal sandwich and $`d\asymp n`$.

Let $`v=\sqrt{a_{k-1}/a_{k+1}}`$. Divide each magnitude $`a_{k+j}v^{k+j}`$ by the central magnitude $`a_kv^k`$. The log correction relative to the unrestricted normalized magnitude is $`\ell_j-\ell_0-j(\ell_1-\ell_{-1})/2`$, where $`\ell_j=\log(a_{k+j}/\binom n{k+j}^d)`$. It tends to zero at each fixed $`j`$, since it is a fixed linear combination of differences among the neighboring log decrements. This step does not require any one decrement to tend to zero.

With $`x=k/n`$, put $`A_n=d/(2nx(1-x))`$. For fixed $`j`$ the unrestricted normalized log magnitude at the geometric radius is $`-A_nj^2+O_j(n^{-1})`$, uniformly on these compact intervals, by Taylor expansion of its binomial second quotients. The normalized capped magnitudes have a uniform exponential bound in $`|j|`$. Indeed both adjacent magnitudes equal $`G_k^{-1/2}\le\exp[-2d/(n+2)]`$ by the orientation curvature bound, and all succeeding ratios are at most this quantity by ordinary log-concavity. The support contains every fixed offset eventually, since both $`k`$ and $`\lfloor nT/d\rfloor`$ diverge.

It follows that after division by the central monomial the capped polynomial converges uniformly on its geometric circle to its varying Gaussian comparison, in the sense that the sup norm of their difference tends to zero. The comparison is

$$
\Theta_{A_n}(\theta)=\sum_{j\in\mathbb Z}e^{-A_nj^2}e^{ij\theta}
=\sqrt{\pi/A_n}\sum_{\ell\in\mathbb Z}
 e^{-(\theta-2\pi\ell)^2/(4A_n)}.
$$

The second identity follows by computing the Fourier coefficients of the periodized Gaussian. The function is positive, with a lower bound uniform over the compact range of $`A_n`$ and the whole circle, by taking the nearest summand. Hence the rotated capped polynomial has positive real part for all angles eventually. It has winding zero and no circle root after normalization, giving exactly $`k`$ zeros inside and the claimed negative-ray sign. Consecutive such indices isolate simple negative roots by alternating signs and the disk counts.

For the fixed-headroom version, replace $`z\to\infty`$ by $`z\ge Z`$ throughout the estimate and choose $`n`$ sufficiently large for $`\log n=o(\sqrt d)`$. The contraction bound can be made arbitrarily small by choosing $`Z`$ large. First fix a truncation radius $`J`$ so both uniform tails are smaller than a fixed fraction of the minimum of $`\Theta_{A_n}`$. Then choose $`Z`$ so the bound $`O(\sup_{z\ge Z}(1+z)e^{-c'z^2})`$ on the slope spread makes the finitely many normalized errors smaller than the remaining margin. The constants then work for every cap and quota in the stated compact range. This is an eventual theorem and does not compute a numerical height cutoff. It treats the high-headroom side of the transition and leaves signs at small or negative standardized headroom open.

The repository already obtains eventual geometric signs in a wider dimension and cap range by a Fourier method, with an explicit but much larger height threshold. The contribution here is the recursion proof on the high-headroom side and its separation of cap-event rarity from variation in the centered local coefficients. The finite scalar certificate is recorded separately. [Earlier geometric sign theorem](https://github.com/ProgramComputer/open-math-research/blob/6a91a65e940e8aa9adadb3be9fe344266eb22d59/topics/balanced-arrays/effective-sublinear/angular-theorem.md)
