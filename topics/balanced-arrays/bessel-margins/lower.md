# Capacity lower bound for prescribed-row balancing probabilities

Let the $n$ independent labeled rows be uniform subsets of $[d]$ of specified sizes $\ell_1,\ldots,\ell_n$, with $\sum_i\ell_i=dk$, $0\le k\le n$. Write $S$ for the column-sum vector and $x=k/n$. Define the binomial mean mass $b_{n,k}=\binom nk x^k(1-x)^{n-k}$, with the natural endpoint value one. Then the finite bounds

$$
\mathbb P(S=k\mathbf1)\ \ge\ b_{n,k}^{\,d-1}\ \ge\ b_{n,k}^{\,d}
$$

hold without an aspect-ratio assumption. For $1/5\le x\le4/5$ one explicit estimate is

$$
\mathbb P(S=k\mathbf1)\ge
 (2\pi n x(1-x))^{-(d-1)/2}
 \exp\!\left(-\frac{25(d-1)}{48n}\right).
$$

These are applications of known capacity bounds.

## Stable generating polynomial and capacity

The generating polynomial is

$$
F(\boldsymbol z)=\mathbb E\,\boldsymbol z^S
=\prod_{i=1}^{n}\frac{e_{\ell_i}(\boldsymbol z)}{\binom d{\ell_i}}.
$$

Elementary symmetric polynomials are real stable, including the constant and monomial endpoints. Thus $F$ is real stable, with nonnegative coefficients, homogeneous of total degree $dk$, and of degree at most $n$ in every variable. Each coordinate of $S$ has mean $k$ by symmetry and the total. For positive real $\boldsymbol z$, put $z_j=e^{t_j}$. The capacity at the balanced exponent is

$$
\mathrm{Cap}_{k\mathbf1}(F)
=\inf_{\boldsymbol t\in\mathbb R^d}
 \mathbb E e^{\boldsymbol t\cdot(S-k\mathbf1)}=1
$$

by Jensen and evaluation at zero. This proof also handles deterministic rows.

## The extraction factor

For a nonzero real-rooted univariate polynomial $f(y)$ with nonnegative coefficients and degree at most $n$, one has

$$
[y^k]f(y)\ \ge\ b_{n,k}\inf_{y>0}\frac{f(y)}{y^k}.
$$

If the capacity vanishes, this is immediate. If $k$ is an extremal exponent, the corresponding boundary limit shows the capacity equals the coefficient. Otherwise the ratio attains its minimum at some $y_*>0$. Factor $f$ over its nonpositive real roots and divide $f(y_*z)$ by $f(y_*)$. The result is the probability generating polynomial of independent Bernoulli trials with successes $p_j$ determined by the factors. Zero roots give deterministic successes, and adding deterministic failures pads the number of trials to $n$. Stationarity of $f(y)/y^k$ means the total expectation of successes is $k$. Hoeffding's Theorem 5, at the interval consisting only of this integer mean, bounds its mass below by the mass of the equal-parameter binomial. Undoing the tilt gives the displayed extraction. [Hoeffding, original report](https://repository.lib.ncsu.edu/bitstream/1840.4/2268/1/ISMS_1955_128.pdf)

For a multivariate real-stable polynomial $P$ with nonnegative coefficients, fix all variables but the last at positive reals and apply this univariate inequality. Stability under real specialization follows by a limit from the upper half-plane, and the restriction here is nonzero. Dividing by the monomial in the remaining variables and taking their infimum proves

$$
\mathrm{Cap}_{\alpha'}([y^k]P)
 \ge b_{n,k}\,\mathrm{Cap}_{(\alpha',k)}(P).
$$

Coefficient extraction preserves stability or gives zero, since it is a derivative followed by specializing at zero and dividing by a factorial. Positive capacity in the iteration excludes zero. Extract $d-1$ columns, retaining degree at most $n$ in each remaining variable. Homogeneity forces the last resulting polynomial to be a constant times $z_d^k$, whose capacity is already the desired coefficient. This yields $b_{n,k}^{d-1}$. When $k=0$ or $k=n$, each row is deterministic and balance has probability one.

This argument is Gurvits's degree-dependent Theorem 5.1, especially its extraction inequality (37) and Lemma 5.4. Its coefficient factor with degree bound $m$ is $\mathrm{vdw}(m)/(\mathrm{vdw}(k)\mathrm{vdw}(m-k))=b_{m,k}$. The author's Example 7.1 uses a product of elementary symmetric polynomials for regular matrices, and his Corollary 7.2 uses arbitrary row sizes with a prescribed support. A companion route gives the weaker stated goal immediately from Gurvits–Leake Theorem 4.4 by testing $F$ against the monomial $z_1^k\cdots z_d^k$ with degree vector $(n,\ldots,n)$. The monomial has capacity one, and their coefficient inner product divides its matching coefficient by $\binom nk^d$. [Gurvits, TR13-141 rev. 1, Thm. 5.1 and §7](https://eccc.weizmann.ac.il/report/2013/141/revision/1/download/) · [Gurvits–Leake, Thm. 4.4](https://doi.org/10.1017/S0963548321000122)

Barvinok's binary-margin Theorem 1.1 uses a joint row-and-column entropy capacity and different factorial factors. Brändén–Leake–Pak discuss the comparison with the subsequent Gurvits bound in §2.5, Theorems 2.7 and 2.9. The single extraction route above works directly in the conditional independent-row model. No novelty claim is made for these inequalities. [Barvinok](https://arxiv.org/abs/0806.1480) · [Brändén–Leake–Pak](https://www.math.ucla.edu/~pak/papers/BCT8.pdf)

## Uniform Stirling error

For $1\le k<n$, write $m!=\sqrt{2\pi m}(m/e)^m e^{R_m}$, where Robbins gives $0<R_m<1/(12m)$. Cancellation in the mean mass yields

$$
b_{n,k}=(2\pi n x(1-x))^{-1/2}e^{\,R_n-R_k-R_{n-k}}
\ge(2\pi n x(1-x))^{-1/2}e^{-1/(12n x(1-x))}.
$$

The exponent bound is at least $-25/(48n)$ for $x\in[1/5,4/5]$. Raising this positive bound to either $d-1$ or $d$ proves the claimed quantitative estimate. This supplies a finite denominator bound, without asserting optimality for the symmetric row model or identifying the exact asymptotic determinant. [Robbins](https://heuklyd.github.io/papers/pdf/Robbins-1955.pdf)
