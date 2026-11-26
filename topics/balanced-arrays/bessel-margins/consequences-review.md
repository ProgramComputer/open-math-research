# Independent review of the near-saturation curvature consequences

**Verdict.** The scalar-to-array transfer, profile averaging and explicit cutoff in [consequences.md](consequences.md) are valid using the established profile bounds in [lower.md](lower.md) and [upper.md](upper.md). For $n\ge\lceil\exp(50)\rceil$, $n/4\le d\le n$, $1\le k<D$, and $h=nr/d-k\le\frac12\sqrt{n/\log n}$, the proof gives strict factor-four curvature and therefore at least $D-k$ distinct negative roots outside the geometric node. The exact terminal checker uses a separate stronger test for simplicity. I found no substantive gap.

## Profile weights and conditioned moments

The scalar coefficient $U_e$ counts arrays by total deficit, so the profile probabilities before imposing balance are proportional to the product of the row binomial factors. The variance statistic $B=\sum_i J_i^2/d^2$ varies with the profile. The corrected scalar consequence of the upper bound uses its expectation under this same law, with the uniform penalty $9e/d$ available as a fallback. The column-balanced coefficient is exactly $a_k=U_eQ_k$.

For independent log-concave integer masses with interval support, the conditional first-coordinate mass at total $s$ is proportional to $b_jc_{s-j}$, with $c$ log-concave by convolution. The likelihood ratio for total $s+1$ against total $s$ is nondecreasing on common support. The ratio for the same comparison after decreasing the first coordinate at total $s+1$ by one is nonincreasing. Conditional support endpoints either stay fixed or increase by one as $s$ grows by one. Therefore both stochastic orders hold, including at endpoints. The common-quantile coupling increases the first coordinate by zero or one. Conditional on those two coordinates, the remaining sums either agree or differ by one, in the correct order. Using the same argument by induction couples the remaining coordinates as required. At a fixed total, increasing any selected coordinate decreases the conditional expected value of a nonnegative increasing function of the others. Pairing it with the selected increasing factor gives nonpositive covariance. Repeating with omitted coordinates assigned the factor one proves the product inequality under the original conditioned distribution.

The marginal of a deficit is log-concave and has mean $\mu=e/n$. Within the positive support, the normalized tail ratios are tail-weighted averages of the decreasing adjacent mass ratios. Before the support they are one, and after the support the tails vanish. Thus $T_{a+b}\le T_aT_b$, including possible support endpoints. The number of compositions of a given sum $s$ into $m$ positive parts is $\binom{s-1}{m-1}$, so summing these tail bounds gives $\mathbb E\binom Jm\le\mu^m$ by the hockey-stick identity. The coefficientwise generating-function bound then applies also after one or two differentiations for nonnegative arguments with $\mu w<1$. Since $J^2/d^2\le J/d$, the estimate $e^y-1\le y e^y$ gives the stated bound on the squared-deficit moment using $t=58/d$. The identity $J^2=J(J-1)+J$ accounts for its two terms. This avoids an exponential constant of order $e^{58}$ in the explicit cutoff.

## Signs, neighboring quotas and explicit constants

At a center with $G_k\le4$, the binomial curvature bound localizes $k$ to $.23n<k<.77n$. For the cutoff in question $n\ge1024$, so all three densities at $k-1,k,k+1$ lie in $[.2,.8]$. If instead $G_k>4$ the desired conclusion already holds. No independent assumption on the cap fraction is needed. The deficits at the three quotas are $d(h+1),dh,d(h-1)$, respectively, and $h\ge1$ follows from $k\le D-1$. Thus all three are feasible and nonnegative, including a zero deficit at the largest quota. The upper profile bound needs the largest deficit to satisfy $h+1\le n/100$, which follows from the explicit cutoff with substantial margin.

The exact logarithmic baseline ratio is

$$
2\log L_k-\log L_{k-1}-\log L_{k+1}
=\frac{d-1}{2}\log[(1-k^{-2})(1-(n-k)^{-2})].
$$

It is negative, and using $k,n-k\ge n/5$ and $d\le n$ gives the stated lower bound $-50/n$. The two upper factors each give $\tfrac12\log d+72$, and the two lower factors at the center cost in total $25(d-1)/(24n)\le25/24$. The stated scalar quotient at deficits $e-d,e,e+d$ applies directly, in either order of the two neighbors. The pinned source contains exactly the bound used. Writing $e=dh$ and $n/d\le4$ gives the simplified lower bound $(n-1)/((h+1)(h+5))$.

Write $\ell=\log n\ge50$. From $\ell\le\sqrt n$ and $n\ge5000^4$ we get $h+5\le.501\sqrt{n/\ell}$, whence the scalar term is bigger than $3.98\ell$. At either neighbor $t\le.001$ and $\mu(e^t-1)\le.001$. In particular the coefficients multiplying $\mu$ and $2\mu^2$ in the exponential-moment estimate are at most $(1000/999)^5<1.01$. Summing the two moment losses uses the exact identities

$$
\frac{n}{d^2}(2\mu_-^2+2\mu_+^2)=\frac{4(h^2+1)}n,
\qquad
\frac{n}{d^2}(\mu_-+\mu_+)=\frac{2h}{d}.
$$

Here $4h^2/n\le1/\ell$ and $4/n+2h/d<.001$, so the loss is less than two. Since $50/n<.01$ and $\log d\le\ell$, the lower bound on $\log G_k$ is larger than $149-144-25/24-2-.01>1.5>\log4$. The logic therefore contradicts $G_k\le4$ at every tested center and works uniformly at the stated endpoint.

All successive internal quotas toward saturation have smaller $h$, so the same theorem applies to them. Strict orientation log-concavity orders the geometric node magnitudes. At each node with $G_k>4$, the immediate terms total less than the central magnitude and consecutive farther terms can be paired with the favorable sign. Along the negative axis, after the node of index $k$ there are exactly $D-k$ disjoint sign-change intervals through the last node and the leading sign at negative infinity. This proves the asserted number of distinct roots on that side. Simplicity does not follow from this count of a proper subset of the degree.

## Exact finite examples and scope

I ran the standard-library [certificate checker](certificates.py) and obtained byte-for-byte agreement with [certificates.jsonl](certificates.jsonl). Its logarithm bound uses $(d-1).\mathrm{bit\_length}()\cdot7/10>\log d$ for the dimensions under test. It obtains a rational upper bound on $e^{58/d}$ from $1/(1-58/d)$ when applying the profile moment bound, and uses the uniform $9e/d$ penalty whenever the resulting denominator fails the positivity test. Its scalar lower bound uses $\log(1+d/e)\ge2d/(2e+d)$. The test $\log G_k>11/5>\log9$ at the first qualifying terminal node makes the full-circle sum of noncentral term magnitudes at most $2/(\sqrt{G_k}-1)<1$ relative to the central monomial. Rouché counts exactly $k$ roots inside the circle. The $D-k$ distinct negative roots supplied by the terminal sign sequence therefore account for all roots outside and are simple. The loop's first failed or out-of-range index is immediately before its certified run, so its reported count $D-k-1$ uses the correct starting index. The numerical outputs are lower bounds on verified root counts.

The asymptotic expansion of the scalar lower bound is $n/h^2+O(n/h^3+1/h^2)$ when $h$ grows, uniformly over this aspect range. At $h\asymp\sqrt{n/\log n}$ the error and averaged extra moment cost tend to zero. The residual $\log d$ penalty is genuine for these input bounds, because the lower and upper prefactors differ by $\sqrt d$. The stated hypothetical matching-prefactor result is conditional and does not enlarge the proved strip.

**Signed** · four_central, independent agent-assisted mathematical review.
