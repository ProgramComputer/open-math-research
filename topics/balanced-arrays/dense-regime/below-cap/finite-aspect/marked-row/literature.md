# Review of overflow comparisons and the geometric-circle count

Independent agent-assisted proof review by Codex (lower_sign_replay), 2026-11-26. The elementary matched-mean comparison is valid and gives a finite sign criterion using an oscillation of extension ratios. It yields the actual geometric-circle count throughout the compact-density range with expected uncapped overflow at most $`n^{3/4-\epsilon}`$ for any fixed $`\epsilon>0`$ and sufficiently large $`n`$. It leaves the fixed-standard-deviation cap transition open. The earlier negative-relation argument gives a separate absolute approximation to the probability of observing no overflow.

Let $`A_k`$ count the labeled $`n\times d`$ cap-$`r`$ arrays with all column sums $`k`$, and let $`B_k=\binom nk^d`$. Write $`P_k=A_k/B_k`$, and $`P(\boldsymbol k)`$ for the analogous normalized validity probability at mixed quotas. Set $`p=k/n`$ and $`T(p)=\Pr(\mathrm{Bin}(d,p)>r)`$. Full cap is understood separately, since then $`T=0`$ and every normalized validity factor is one. The discussion below assumes $`1\le r<d`$.

## Two-sided endpoint comparison

Let $`J`$ denote the size of a single row in the uniform capped fiber with balanced quota $`k`$. Its mass at $`j`$ is proportional to $`\binom dj F_j`$, where $`F_j`$ counts arrays on the remaining $`n-1`$ rows with quota $`k-1`$ in $`j`$ columns and $`k`$ in the others. The binomial factor follows by symmetry of the column labels. If $`F_j>0`$, lowering one more column quota preserves feasibility, so the support of $`F_j`$ within $`0,\ldots,r`$ is contiguous. The mixed orientation inequality applied to a base with $`j+1`$ lowered quotas and two of those coordinates raised gives $`F_j^2\ge F_{j-1}F_{j+1}`$. This is exactly the weighted-or-unweighted mixed comparison already proved for cap arrays, with all remaining rows subject to the same original cap. [Repository orientation theorem and mixed inequality](https://github.com/ProgramComputer/open-math-research/blob/research/topics/balanced-arrays/orientation-normalization.md).

For a parameter $`q`$, let $`Q_j(q)`$ be the mass at $`j`$ of $`\mathrm{Bin}(d,q)`$ conditioned to be at most $`r`$, and let $`p_{\ast}`$ be its parameter with mean $`dp`$ when $`0<dp<r`$. The actual row size also has that mean by exchangeability and the deterministic total $`dk`$. The ratio of the actual mass to $`Q_j(p_{\ast})`$ is proportional to $`F_j/(p_{\ast}/(1-p_{\ast}))^j`$, hence log-concave. Its superlevel set at one is an interval. If the actual mass were larger at $`r`$, the signed mass difference would have only one sign change, from nonpositive to nonnegative, ending positively at $`r`$. This would give a larger mean by subtracting the threshold from the index in the expectation of the signed masses. Thus $`\Pr(J=r)\le Q_r(p_{\ast})`$. More generally the two crossings give convex order against the matched law. [Relative log-concavity and convex order](https://doi.org/10.1017/s0269964823000293).

For the lower bound, divide the residual count by its column binomial normalizations. The factor from that normalization is proportional to $`(p/(1-p))^j`$ because $`\binom{n-1}{k-1}/\binom{n-1}{k}=p/(1-p)`$. The residual normalized validity is nondecreasing in $`j`$, by nesting uniform column subsets when quotas are lowered. Thus the likelihood ratio of the actual mass to $`Q_j(p)`$ is nondecreasing in $`j`$. Its value at $`r`$ is at least its mean one under $`Q(p)`$, so $`\Pr(J=r)\ge Q_r(p)`$.

One uniform insertion into an unused location of column $`i`$ turns its uniform $`k`$-subset into a uniform $`(k+1)`$-subset. It preserves legality precisely when the chosen row is unsaturated. At a balanced input a given row has probability $`(d-r)/d`$ to leave column $`i`$ empty given that it is saturated. Consequently the exact normalized extension loss at a balanced input is

$$
\ell(p)=1-\frac{P(k\mathbf1+e_i)}{P(k\mathbf1)}
=\frac{d-r}{d(1-p)}\Pr(J=r).
$$

The cancellation $`\Pr(\mathrm{Bin}(d,q)=r)=(1-q)T'(q)/(d-r)`$, obtained by differentiating the tail, therefore gives

$$
\ell_-(p)=\frac{T'(p)}{d(1-T(p))}
\quad\le\quad \ell(p)\quad\le\quad
\ell_+(p)=\frac{1-p_{\ast}}{1-p}\frac{T'(p_{\ast})}{d(1-T(p_{\ast}))}.
$$

A rational upper bracket $`p_+^*\ge p_{\ast}`$ can also be used by evaluating $`Q_r(p_+^*)`$ directly. Its monotonicity follows by differentiation in log odds, with derivative $`Q_r(q)(r-\mathrm E_q[J])\ge0`$. Using this monotonicity, the upper endpoint test itself can be performed with exact binomial weights and rational inequalities.

## Effective comparison of the two losses

Take $`p\in[\gamma,1-\gamma]`$ with $`0<\gamma\le1/2`$, write $`T=T(p)`$, and set $`H=\sqrt{\log(e/T)}`$. The one-sided Hoeffding bound, integrated above $`z=\sqrt{d\log(e/T)/2}`$, gives

$$
0\le\mathrm E[(X-dp)\mathbf1_{X>r}]\le \sqrt d  T H,
\qquad X\sim\mathrm{Bin}(d,p).
$$

For the upper bound, the integral of the tail costs at most $`d e^{-2z^2/d}/(4z)`$ beyond $`zT`$. Nonnegativity follows from the covariance of two increasing functions of $`X`$. Since $`T'(p)=\mathrm E[(X-dp)\mathbf1_{X>r}]/(p(1-p))`$, this also bounds the tail derivative.

Suppose $`TH^2\le\gamma/32`$. Put $`q=p+4TH/\sqrt d`$, which is at most $`p+\gamma/8`$. Along this interval the binomial variance factor $`u(1-u)`$ is at least $`\gamma/4`$. The derivative of $`H(u)=\sqrt{\log(e/T(u))}`$ is at least $`-2\sqrt d/\gamma`$. Hence $`\log(T(q)/T)\le16TH^2/\gamma\le1/2`$ and $`T(q)\le2T`$. The truncated mean at $`p`$ is at most $`dp`$. The truncated mean at $`q`$ is at least $`dq-\sqrt d\,(2T)H/(1-2T)>dp`$, proving that $`p_{\ast}`$ exists and $`0\le p_{\ast}-p\le4TH/\sqrt d`$. The simple bound $`\ell_+(p)\le9TH/(\gamma\sqrt d)`$ follows directly from the formula above for $`\ell_+`$, since $`T(p_{\ast})\le2T`$ and $`H(p_{\ast})\le H`$.

To compare the losses more sharply, note that throughout this tilt interval $`T(u)\le2T<1/2`$. Hoeffding on the right or left according to the sign of $`r-du`$ gives $`|r-du|\le\sqrt d\,H(u)`$. Thus the binomial pivotal mass identity yields

$$
\left|\frac{d}{du}\log T'(u)\right|
=\frac{|r-(d-1)u|}{u(1-u)}
\le \frac8\gamma\sqrt d H(u).
$$

After integration from $`p`$ to $`p_{\ast}`$, including the truncation normalizer and using $`(1-p_{\ast})/(1-p)\le1`$, it follows that $`\log(\ell_+(p)/\ell_-(p))\le34TH^2/\gamma`$. This bound is at most $`17/16`$, where $`e^x-1\le3x`$. Since $`\ell_-(p)\le4TH/(\gamma\sqrt d)`$, the resulting width bound is

$$
0\le\ell_+(p)-\ell_-(p)
\le \frac{408}{\gamma^2\sqrt d}T^2H^3.
$$

On a density interval inside $`[\gamma,1-\gamma]`$ where $`T(u)<1/2`$, the same pivotal derivative calculation and $`T'(u)/(1-T(u))`$ give $`|\ell_-'(u)|\le32 T(u)H(u)^2/\gamma^2`$. In deriving this use $`u(1-u)\ge\gamma/2`$, $`H(u)\ge1`$, and the bound on the tail derivative. Both $`T H^2`$ and $`T^2H^3`$ increase with $`T`$ on $`0<T\le1`$.

Take $`p_-= (k-2)/n`$ and $`p_+=(k+2)/n`$, both in the compact density interval. Now let $`T`$ and $`H`$ stand for their values at $`p_+`$. Coordinatewise antitonicity of the actual extension factors sandwiches every mixed extension between the endpoint factors. The lower endpoint is feasible by deletion, and the upper endpoint has $`dp_+<r`$ by the matched-tilt argument. Its extension loss is bounded by $`\ell_+(p_+)<1`$, so the upper comparison also has a positive factor. Hence the four adjacent diagonal log slopes $`s_j=\log P_j-\log P_{j-1}`$ for $`j=k-1,\ldots,k+2`$ are nonincreasing and belong to an interval of width at most

$$
\tau=d\log\frac{1-\ell_-(p_-)}{1-\ell_+(p_+)}
\le\frac{816\sqrt d T^2H^3+256(d/n)TH^2}{\gamma^2}.
$$

Indeed only the endpoint difference of the losses matters. Split it into the matching-tilt width at $`p_+`$ and the variation of $`\ell_-`$ from $`p_-`$ to $`p_+`$. Use $`1/(1-\ell_+(p_+))\le2`$, valid by $`TH^2\le\gamma/32`$. A direct numerical version uses endpoint brackets itself and the elementary criterion $`4d(\ell_+(p_+)-\ell_-(p_-))\le1-\ell_+(p_+)`$ for $`\tau\le1/4`$. The same argument works for a block of center indices by taking its outer endpoint quotas.

## From a slope interval to an exact geometric-circle count

Let $`u_0=\sqrt{B_{k-1}/B_{k+1}}`$ and $`u=\sqrt{A_{k-1}/A_{k+1}}`$. For an offset $`j`$ put $`w_j^0=B_{k+j}u_0^j/B_k`$, and write the actual normalized magnitude as $`w_j=w_j^0q_j`$. Here $`q_j`$ is exactly the normalized cap factor at its own geometric radius. Normalized log-concavity implies $`q_j\le1`$ at all supported offsets and the same comparison holds with $`q_j=0`$ outside the capped support. In particular odd cap corrections improve the signed sum, while the correction to the even terms must be controlled.

Write $`A=s_k-s_{k+1}`$, $`B=s_{k-1}-s_k`$, and $`C=s_{k+1}-s_{k+2}`$, so $`A,B,C\ge0`$ and $`A+B+C\le\tau`$. The first two offsets have the exact cap factors

$$
q_{\pm 1}=e^{-A/2},\qquad q_{-2}=e^{-A-B},\qquad q_2=e^{-A-C}.
$$

The gain at the two first neighbors is at least the loss from the common factor $`e^{-A}`$ on the two second neighbors if $`w_{-1}^0+w_1^0\ge2(w_{-2}^0+w_2^0)`$. The rest of the loss in the signed window $`|j|\le3`$ is at most

$$
2\max(w_{-2}^0,w_2^0)\left(1-e^{-(B+C)/2}\right).
$$

This follows from $`2-e^{-B}-e^{-C}\le2(1-e^{-(B+C)/2})`$. Outward pairs starting at distance four have nonnegative total, since the magnitudes decrease at the actual geometric radius by log-concavity. Thus the actual signed value is positive whenever the unrestricted seven-term parity exceeds the displayed loss. This argument only needs feasibility through $`k+2`$.

For example, let $`n\ge10^6`$, $`n/4\le d\le n/2`$, and $`k/n\in[1/4,3/4]`$. The minimum unrestricted log curvature is at least $`n/(n+2)`$, using $`\log(1+2/n)\ge2/(n+2)`$. Hence $`w_2^0,w_{-2}^0<.136`$ and the first-neighbor magnitudes are more than twice their respective second-neighbor magnitudes. The unrestricted seven-term parity is greater than $`.032`$ at its geometric radius. To see this directly, let $`a`$ be half the unrestricted log curvature at $`k`$. The derivative of the real interpolation of the log curvature is bounded on $`[k-2,k+2]`$ by $`25/n`$, since both a quota and its complement there exceed $`n/5`$. Exact recursion for the normalized coefficients then gives $`w_{\pm1}^0=e^{-a}`$, errors at most $`25/n`$ in the exponents $`-4a`$, and errors at most $`100/n`$ in the exponents $`-9a`$. Relative to $`m(a)=1-2e^{-a}+2e^{-4a}-2e^{-9a}`$, these errors cost at most $`450/n`$. The function is increasing for $`a\ge n/(2(n+2))`$ from $`e^{3a}>4`$, and $`a\ge1/2-1/n`$. The error from replacing its minimum by $`m(1/2)`$ is at most $`28/n`$ by its derivative bound. Using $`e^{-1/2}<.607`$, $`e^{-2}>.135`$ and $`e^{-9/2}<.0112`$ gives $`m(1/2)>.0336`$. Therefore the seven-term parity is greater than $`.032`$ after all errors. For $`\tau\le1/4`$ the parity loss is at most $`2(.136)(1-e^{-1/8})<.032`$, the last inequality following from $`1-e^{-1/8}\le361/3072`$.

The actual quotient bound is at least the unrestricted one and exceeds $`9/4`$. Hence the strict signed value implies exactly $`k`$ roots strictly inside the actual geometric circle with a free boundary. The usual log-concavity gives increasing geometric radii, so consecutive certified counts and signs isolate single simple negative roots between them. [Sharp one-sign disk-count theorem](https://github.com/ProgramComputer/open-math-research/blob/8c799d583509ae03f3e3caabc0e3d02449695f15/topics/balanced-arrays/root-distributions/single-sign/README.md).

On any fixed compact density interval the same unrestricted parity estimates hold for sufficiently large $`n`$, with the curvature derivative constant adjusted for its distance to the endpoints. At the center suppose $`nT(k/n)\le n^{3/4-\epsilon}`$ with $`0<\epsilon<3/4`$. On the interval up to $`(k+2)/n`$ the tail derivative bound and a first-exit argument give $`T((k+2)/n)\le2n^{-1/4-\epsilon}`$ for all sufficiently large $`n`$. Indeed below that exit value the derivative is bounded by a constant times $`\sqrt d\,n^{-1/4-\epsilon}\sqrt{\log n}`$, and the interval length is $`2/n`$. In the slope bound the two terms are then respectively $`O_\gamma(n^{-2\epsilon}\log^{3/2}n)`$ and $`O_\gamma(n^{-1/4-\epsilon}\log n)`$. They vanish, proving the claimed expected-overflow range. This uses the relative change of nearby coefficient ratios and does not require an absolute lower bound on the normalized probability of validity.

## Independent check of the negative-relation estimate

Under independently chosen uniform $`k`$-subsets for the columns, let $`I_i=\mathbf1_{\{\text{row }i\text{ exceeds }r\}}`$, $`W=\sum_iI_i`$, and $`\lambda=nT(p)`$. Couple the row-one sizes $`S`$ and $`S^*`$ under the ordinary and conditional-on-overflow laws so that $`S^*\ge S`$, and use the first $`S`$ or $`S^*`$ entries of the same uniform column permutation for the occupied columns of that row. Given the resulting first rows, use a uniform common permutation of the remaining rows in each column, consuming $`k-1`$ positions if row one is occupied and $`k`$ otherwise. The conditioned first row is larger and every other row decreases entrywise. Thus $`W^*=(W-I_1\mid I_1=1)\le W-I_1`$ in the coupling.

For $`f(v)=\mathrm E(1-v)^W`$ on $`[0,1]`$, exchangeability gives $`-f'(v)=\lambda\mathrm E(1-v)^{W^*}`$. Telescoping the difference of the two powers in the coupling bounds $`-f'(v)-\lambda f(v)`$ between zero and $`v(\lambda-\mathrm{Var}(W))`$, since $`\mathrm E W^*=\mathrm E W^2/\lambda-1`$. Integration yields

$$
0\le e^{-\lambda}-P_k\le
(\lambda-\mathrm{Var}(W))\frac{\lambda-1+e^{-\lambda}}{\lambda^2}
\le\frac{\lambda-\mathrm{Var}(W)}\lambda.
$$

The final ratio equals $`T+(n-1)(T-\Pr(I_2=1\mid I_1=1))`$. Comparing the conditioned second row to all cells of parameter $`(k-1)/(n-1)`$ immediately gives the proposed crude bound. The coupled changes improve it. The expected number of changed columns is $`\mathrm E(S^*-S)\le\sqrt d\,H`$. Each change decreases row two's overflow probability by at most $`1/(n-1)`$ times its pivotal atom in the other $`d-1`$ cells. In any intermediate mixed law, each of those Bernoulli probabilities differs from $`p`$ by at most $`1/(n-1)`$. The product likelihood ratio relative to iid $`p`$ is bounded by $`\exp(C_\gamma d/(n-1))`$ on each cell assignment, uniformly bounded in the aspect range. The iid pivotal atom is $`T'(p)/d\le C_\gamma TH/\sqrt d`$. Consequently the pair deficit is at most $`C_\gamma TH^2/(n-1)`$, and the absolute Poisson error is $`O_\gamma(TH^2)`$. At $`\lambda\le(1-\epsilon)\log n`$ this error is $`o(e^{-\lambda})`$. Applying this at any fixed nearby quotas, the derivative bound also gives $`\lambda_{k+j}-\lambda_k=o(1)`$. Hence $`P_{k+j}/P_k\to1`$ for fixed $`j`$ in that range. A fixed window then suffices for the circle signs by global log-concavity. The later two-sided extension estimate reaches beyond this logarithmic regime without approximating $`P_k`$ itself.

## Prior work and search scope

The paired mixed comparison is an application of the Kahn–Neiman orientation theorem already used in the repository. The extra statements here are the marked-row choice of residual quotas, the two-sided comparison with distinct truncated binomial tilts, and its use to bound the local oscillation of cap loss. The upper comparison uses the classical crossing criterion for relative log-concavity. The lower comparison uses only nested column subsets of the remaining rows. Both arguments retain the labeled sampling-without-replacement model. [Kahn and Neiman, §4, Lemma 8](https://doi.org/10.1002/rsa.20395), [author preprint](https://arxiv.org/pdf/1001.0610#page=9), [earlier repository orientation comparison](https://github.com/ProgramComputer/open-math-research/blob/research/topics/balanced-arrays/orientation-normalization.md).

The negative-relation coupling fits the usual Stein–Chen framework. Barbour, Holst and Janson's negatively related indicator bound uses $`\lambda-\mathrm{Var}(W)`$, and the coupling definition is explicit in Chen and Xia. McKay and Skerman's independent-binomial comparison for fixed-column degree sequences is a related route to a relative void probability. The finite orientation comparison above needs no dense margin enumeration error. The earlier rare-overflow proof bounds the cap loss itself by a union bound, whereas the present sign proof bounds a change of nearby log coefficient ratios. [Chen's dependent-indicator method](https://bpb-us-w2.wpmucdn.com/blog.nus.edu.sg/dist/3/10976/files/2019/01/Poisson_approx_for_dep_trials-rdomqz.pdf), [Chen and Xia, Proposition 4.5 and its preceding definition](https://bpb-us-w2.wpmucdn.com/blog.nus.edu.sg/dist/3/10976/files/2019/01/AOP283-19cu9pw.pdf), [McKay and Skerman](https://arxiv.org/abs/1302.2446), [earlier finite rare-overflow proof](https://github.com/ProgramComputer/open-math-research/blob/research/topics/balanced-arrays/dense-regime/below-cap/finite-aspect/angular-review.md).

I searched scholarly and web sources on 2026-11-26 for negative relation and Stein–Chen void probabilities, capped fixed-margin arrays, relative log-concavity and truncated-binomial convex order. GitHub code search for “overflow,” “Stein” and “balanced arrays,” and issue search for “balanced arrays,” “overflow” and “Chen,” yielded no hits. The native X search for “balanced arrays,” “overflow” and “Stein” returned HTTP 403, limiting coverage to available web indexing. The cited sources provide the methodological antecedents above. This review makes no priority claim. [X query](https://x.com/search?q=%22balanced%20arrays%22%20%22overflow%22%20%22Stein%22&src=typed_query).
