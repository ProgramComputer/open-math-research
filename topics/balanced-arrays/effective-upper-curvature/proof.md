# An effective upper-edge coefficient inequality for actual balanced arrays

For $`n`$ rows, $`d\ge2`$ columns and cap $`1\le r<d`$, let $`a_k`$ count the labeled arrays with common column quota $`k`$, and put $`D=\lfloor nr/d\rfloor`$. Fix any internal quota $`1\le k<D`$. Define

$$
p=r/d,\qquad e=nr-dk,\qquad M=e+d,\qquad B=n-M .
$$

If $`B>0`$ and $`B\min(p,1-p)\ge2M`$, the following nonasymptotic estimate holds:

$$
\log\frac{a_k^2}{a_{k-1}a_{k+1}}
\ \ge\ \frac{d(n-1)}{n+M-1}\log(1+d/e)-\frac{24dM}{B}.
$$

In particular, if also $`192M^2\le Bd`$ and $`4M\le d^2`$, then $`a_k^2>4a_{k-1}a_{k+1}`$. At its geometric radius $`t_k=\sqrt{a_{k-1}/a_{k+1}}`$ the original polynomial has the sign $`(-1)^k`$. These conditions persist at all larger internal quotas. If $`k`$ is the smallest quota at which the three displayed conditions hold, there are at least $`D-k`$ distinct negative zeros on the side $`q<-t_k`$, one per subsequent sign interval including infinity. The theorem concerns actual finite labeled array counts; it does not require a limiting coefficient model.

## Regular rows and a change of two column margins

Let $`C(\mathbf u)>0`$ count matrices with $`B`$ rows all of size $`r`$, with integer column margins $`\mathbf u`$. Put $`\Delta=u_i-u_j\ge0`$, assuming $`0<u_j`$, $`u_i<B`$. In a random uniform such matrix put $`X=\#\{a:A_{aj}=1,A_{ai}=0\}`$. Fix all entries outside these two columns. Each row needs zero, one or two more entries. Rows needing one split into $`X`$ assigned to $`j`$ and $`X+\Delta`$ assigned to $`i`$. On this conditional fiber the ratio after moving one unit from $`j`$ to $`i`$ equals $`X/(X+\Delta+1)`$ by binomial coefficients. Any fiber available after the move also occurs before it, since the new difference is $`\Delta+2`$. Averaging over baseline fibers gives the exact ratio.

The missing cells of one distinguished row have stable generating polynomial

$$
[z^{\mathbf u}]\ e_r(z)^{B-1}\prod_{\ell=1}^d(x_\ell+z_\ell).
$$

The coefficient constraints force the distinguished row to have size $`r`$. Elementary symmetric polynomials are stable, as are products, and coefficient extraction preserves stability or gives zero, by differentiation and real specialization. The polynomial is nonzero by feasibility. The Rayleigh inequality at positive real variables for a stable multiaffine polynomial gives pairwise negative correlation, also for the complementary occupied cells. By exchangeability of the rows, $`\mathbb EX\ge u_j(1-u_i/B)`$.

Condition next on the row set $`I`$ occupied by column $`i`$. For column $`j`$, the same construction with rows and columns interchanged gives a stable generating polynomial for its holes. The other columns enter with factors $`e_{u_\ell}`$ and the targeted row margins are $`r-\mathbf1_I`$. Mark only holes outside $`I`$ by a common variable, specializing the others to one. This univariate probability generating polynomial has only nonpositive real roots. Reversing it with the total number of available row positions outside $`I`$ gives the probability generating polynomial for $`X`$. It is therefore a product of Bernoulli generating functions, including any deterministic successes. The conditional distribution is identical for each $`I`$ by row symmetry. In particular $`\mathrm{Var}(X)\le\mathbb EX`$. By Cauchy–Schwarz applied to $`\sqrt{X/(X+\Delta+1)}`$ and $`\sqrt{X(X+\Delta+1)}`$,

$$
\frac{C(\mathbf u+\mathbf e_i-\mathbf e_j)}{C(\mathbf u)}
\ \ge\ \frac{\mathbb EX}{\mathbb EX+\Delta+2}.
$$

The reverse-balancing ratio is also at most one by its exact expectation. These bounds use the actual matrix counts.

## Comparison with a common bulk

For any of the three quotas $`k-1,k,k+1`$, the total deficit relative to all rows having size $`r`$ is at most $`M`$. For any row profile of that total, at most $`M`$ rows have size below $`r`$. Permute rows to put $`B`$ full rows first. In the independent uniform subset model conditional on that row profile, let $`W_i`$ count cells of column $`i`$ in the remaining $`M`$ rows. To reach the common quota $`k'`$ the first $`B`$ rows must have margins $`u_i=k'-W_i`$. All have mean $`\mu=Br/d`$ and $`|u_i-\mu|\le M`$. Let $`\mathbf b`$ be a most-balanced margin vector with that fixed total $`Br`$, and put $`C_\star=C(\mathbf b)>0`$. It is feasible by filling each row with a consecutive group of $`r`$ labels in repeated cyclic column order. All permutations of $`\mathbf b`$ have the same count.

To go from $`\mathbf u`$ toward a most-balanced vector, repeatedly move one unit from a larger coordinate to a smaller one whose difference is at least two. This process terminates, because it decreases the sum of squared coordinates. Reverse this path starting at the terminal permutation of $`\mathbf b`$. At all intermediate steps coordinates stay in $`[\mu-M,\mu+M]`$. Thus $`u_j(1-u_i/B)\ge L=Bp(1-p)/4`$ at each reverse move, by the assumption $`B\min(p,1-p)\ge2M`$. Starting at a feasible vector, the lower ratio above grants feasibility at the next step. The energy $`H(\mathbf u)=\sum_i(u_i-\mu)^2`$ increases at a reverse move by $`2(\Delta+1)`$. Its log-count loss is at most $`(\Delta+2)/L\le 2(\Delta+1)/L`$ by $`\log(1+y)\le y`$. Hence

$$
C_\star\exp[-H(\mathbf u)/L]\le C(\mathbf u)\le C_\star.
$$

For a specified row size $`s`$, each of its column indicators is Bernoulli of mean $`s/d`$. Independence over rows gives $`\mathbb EH=\sum_{\text{last rows}}s(1-s/d)`$. With $`s=r-j`$, each summand is at most $`dp(1-p)+j`$, as is seen by expansion. The sum of these $`j`$ is at most $`M`$, and $`dp(1-p)\ge1/2`$. Consequently $`\mathbb EH\le3Md p(1-p)`$. After averaging the matrix count over the last rows, Jensen's inequality gives a balance probability between $`p_\star\exp[-12 Md/B]`$ and $`p_\star`$, with $`p_\star=C_\star/\binom dr^B`$. These bounds are uniform over all the profiles at all three quotas. In particular the same bulk normalizer applies to each quota even when one quota is exactly saturated.

Write $`U_j=[z^j](\sum_{\ell=0}^r\binom d{r-\ell}z^\ell)^n`$ for the unconditioned scalar row-deficit count. Averaging the probability bounds over the appropriate profiles gives $`p_\star\exp[-12Md/B]\le a_{k'}/U_{nr-dk'}\le p_\star`$. The negative-binomial normalization of $`U`$ established in the [scalar deficit lemma](https://github.com/ProgramComputer/open-math-research/blob/ccd2cd0eaaf9555d680ea405a5cc013176fcd7e2/topics/balanced-arrays/deficit-curvature/scalar.md#exact-d-step-bound) gives $`\log(U_e^2/(U_{e-d}U_{e+d}))\ge d(n-1)\log(1+d/e)/(n+M-1)`$. Combining proves the claimed inequality.

Since $`n\ge M+1`$, the scalar lower bound is at least $`d^2/(2M)`$, using $`\log(1+d/e)\ge d/M`$. Under $`192 M^2\le Bd`$, the correction is at most $`d^2/(8M)`$. Under $`4M\le d^2`$ the resulting lower bound is at least $`3/2>\log4`$. All three conditions improve as $`k`$ increases. The [orientation theorem](https://github.com/ProgramComputer/open-math-research/blob/ccd2cd0eaaf9555d680ea405a5cc013176fcd7e2/topics/balanced-arrays/orientation-normalization.md) gives global log-concavity and ordering of the geometric radii. At a quota with curvature exceeding four each neighbor contributes less than half the central term, and the alternating tails from distance two outward have nonnegative normalized sign. This supplies the signs and root intervals asserted above.

The switching precedent and negative-dependence inputs are documented separately. [Primary sources and scope](regular-margin-ratio-prior.md)

## Simple outer zeros

Under the same bulk and quadratic conditions, strengthen the last requirement to $`6M\le d^2`$. Then $`\log\Gamma_k\ge9/4>\log9`$, where $`\Gamma_k=a_k^2/(a_{k-1}a_{k+1})`$. For instance $`e^{9/8}>3`$ follows already by summing its first five Taylor terms. On $`|q|=t_k`$, each neighbor of the $`k`$th monomial has relative magnitude $`\Gamma_k^{-1/2}`$. Log-concavity bounds the successive terms going away from the center in either direction by the same geometric ratio. The sum of the relative magnitudes of all other terms is at most $`2/(\sqrt{\Gamma_k}-1)<1`$. Rouché's theorem thus places exactly $`k`$ zeros, with multiplicity, inside this circle and none on the circle. The already proved signs give $`D-k`$ distinct negative roots outside, so every one of them is simple. For $`(n,r,d)=(10^8,50,100)`$, the two integer tests certify 24 distinct negative roots in the outer intervals, with the 15 most distant roots simple and separated from all remaining roots by a circle.

## Stronger exact examples from the raw estimate

With $`B>0`$ and $`B\min(p,1-p)\ge2M`$, lower-bound the logarithm in the original estimate by $`\log(1+x)\ge 2x/(2+x)`$ at $`x=d/e`$. The inequality follows by differentiating the difference, which is zero at $`x=0`$ and has derivative $`x^2/[(1+x)(2+x)^2]\ge0`$. The resulting rational bound for $`\log\Gamma_k`$ is

$$
\frac{2d^2(n-1)}{(n+M-1)(2e+d)}-\frac{24dM}{B}.
$$

It increases as $`k`$ increases, because $`e`$ and $`M`$ decrease and $`B`$ increases. The bulk hypothesis also persists. A bound above $`139/100>\log4`$ supplies the sign intervals, and one above $`11/5>\log9`$ makes the circle strictly dominated by its central monomial. Both numeric comparisons follow from the first six terms of the positive exponential series, using $`e^{139/200}>2`$ and $`e^{11/10}>3`$.

The replay certifies at least four distinct negative outer roots, including at least three simple outer roots, for $`(n,r,d)=(20000,10,20)`$. For $`(10^8,50,100)`$ it certifies at least 64 distinct negative outer roots, including at least 42 simple outer roots. The two thresholds generally use different circles and geometric nodes. These are evaluations of sufficient criteria for the actual polynomial. The examples require no computation of its coefficient vector and imply no maximality of the root counts.
