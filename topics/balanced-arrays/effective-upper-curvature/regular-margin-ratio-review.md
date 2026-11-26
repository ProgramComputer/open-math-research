# Independent review of regular-row margin switching

**Verdict.** The exact ratio, the stability arguments, and the stated lower bound hold under $`C(\mathbf u)>0`$, $`u_i\ge u_j>0`$, and $`u_i<n`$. A second-moment argument also gives a positive lower bound that yields the quadratic cost for every target margin in the interior.

## Exact ratio and first moment

Fix the columns other than $`i,j`$. Their entries and the row size $`r`$ prescribe which rows must take zero, one, or both of the two columns. If a fiber meets the original margin, let $`b`$ be the number of rows taking both. Among the singly occupied rows there are $`X=u_j-b`$ taking $`j`$ and $`X+\Delta`$ taking $`i`$, where $`\Delta=u_i-u_j`$. The fiber count before the change is $`\binom{2X+\Delta}{X}`$. After the change it is $`\binom{2X+\Delta}{X-1}`$, interpreted as zero for $`X=0`$. Every nonempty shifted fiber also has a nonempty original fiber. In the shifted fiber the number of rows taking $`i`$ alone exceeds the number taking $`j`$ alone by $`\Delta+2`$, so an $`i`$-only row can be switched back. The fiber ratios thus average to

$$
R=\frac{C(\mathbf u+e_i-e_j)}{C(\mathbf u)}
=\mathbb E\frac{X}{X+\Delta+1}.
$$

For a fixed row, the hole generating polynomial is

$$
[z^{\mathbf u}]\prod_{a=1}^d(x_a+z_a)e_r(z)^{n-1}.
$$

Choosing $`x_a`$ marks a hole in that row, and choosing $`z_a`$ contributes one to its column sum. The factors are stable. Stability of $`e_r`$ follows by differentiating $`\prod_a(t+z_a)`$ in $`t`$ and evaluating at zero. Coefficient extraction in the $`z`$ variables preserves stability by differentiation and real specialization. The extracted polynomial is nonzero since its value at all $`x_a=1`$ is $`C(\mathbf u)`$. Pairwise negative correlation follows by setting the other activities to one and using the bivariate multiaffine stability implication $`BC\ge AD`$ for $`A+Bx+Cy+Dxy`$. The covariance of the two indicators is unchanged on replacing both holes by ones. Row exchangeability then gives

$$
\mu=\mathbb E X\ge n\frac{u_j}{n}\left(1-\frac{u_i}{n}\right)
=u_j(1-u_i/n)>0.
$$

## Conditional law and quantitative bound

Fix the row set $`I`$ of column $`i`$. On deleting that column, the remaining row quotas are $`\rho_t=r-\mathbf1_{\{t\in I\}}`$. The hole generating polynomial for column $`j`$ in this conditional family, with variables indexed by rows, is

$$
[z^{\boldsymbol\rho}]\prod_{t=1}^n(x_t+z_t)
\prod_{a\notin\lbrace i,j\rbrace }e_{u_a}(z).
$$

The same stability argument applies. Identifying the activities outside $`I`$ and setting the remaining activities to one gives a univariate polynomial for the number of holes outside $`I`$. It is nonzero, stable, and has nonnegative real coefficients, so its zeros are all nonpositive. Reversing with respect to $`n-u_i`$ counts the ones instead. Its normalized factorization is a Bernoulli product. Zeros at the origin and any missing top degree are compatible with deterministic Bernoulli factors. All row sets $`I`$ of size $`u_i`$ give the same conditional law by row permutations, so $`X`$ itself is Poisson-binomial.

Writing $`\mathbb E[t^X]=\prod_a(1-p_a+p_at)`$ with $`\sum_a p_a=\mu`$, one has

$$
\mathbb E\frac1{X+1}=\int_0^1\mathbb E[t^X]\thinspace dt
\le (1-e^{-\mu})/\mu\le1/\mu .
$$

Together with the exact identity, this gives the claimed $`R\ge1-(\Delta+1)/[u_j(1-u_i/n)]`$. For an always-positive bound, Cauchy–Schwarz applied to the factors $`\sqrt{X/(X+\Delta+1)}`$ and $`\sqrt{X(X+\Delta+1)}`$ gives $`\mu^2\le R\mathbb E[X(X+\Delta+1)]`$. As $`\mathrm{Var}(X)\le\mu`$, this yields

$$
R\ge\frac{\mu}{\mu+\Delta+2}.
$$

The assumptions also imply $`R<1`$. The cases $`r=0`$, $`r=d`$, $`d=1`$, and $`n\le1`$ have no pair satisfying the hypotheses.

## Iteration and scope

For an interior target $`\mathbf v`$ with total $`nr`$, balance it by moving one unit from a maximum coordinate to a minimum whenever they differ by at least two. This reaches a most-balanced vector $`\mathbf b`$. All intermediate coordinates stay between $`\min v_i`$ and $`\max v_i`$. The margins are feasible because successive column counts can be assigned to runs in the cyclic row order. Each run has length at most $`n`$, and the total length $`nr`$ visits each row exactly $`r`$ times. Reverse the path. Each reverse step has receiver at least as large as donor. Let $`L=(\min v_i)(1-\max v_i/n)>0`$ and $`H(\mathbf v)=\sum_i(v_i-nr/d)^2`$. The positive ratio bound gives $`\log R\ge-(\Delta+2)/L\ge-2(\Delta+1)/L`$. In each step $`H`$ increases by exactly $`2(\Delta+1)`$. Thus

$$
\frac{C(\mathbf v)}{C(\mathbf b)}
\ge \exp\negthinspace \left(-\frac{H(\mathbf v)-H(\mathbf b)}{L}\right).
$$

The same reverse balancing and the exact ratio establish maximality of the most-balanced counts. The uniform quadratic bound stated here uses an interior target, so its denominator is positive.

At true saturation $`dk=nr`$, the cap forces all rows to have size $`r`$. For nonzero deficit, applying this lemma to the cap count requires conditioning on the irregular rows and treating the residual regular block. Comparing or summing those contributions is a separate step. The present switch preserves the total and gives no direct comparison between balanced quotas with different totals.

I independently enumerated all labeled regular-row arrays for $`2\le n,d\le4`$ and $`1\le r<d`$. Fixing the first two columns as the ordered pair gave 77 eligible margin cases and 305 conditional row sets. Exact arithmetic verified the fiber ratio, the first-moment and reciprocal-moment inequalities, and both ratio bounds. Rational Sturm counts on the square-free conditional generating polynomials confirmed all their zeros were real.

**Signed** — Independent mathematical reviewer, agent-assisted.
