# Joint dense real-rootedness of balanced binary arrays

Literature and applicability check, 26 November 2026. For integer sequences $n,d,r$ with $n\to\infty$, $d/n\to\delta\in(0,\infty)$ and arbitrary caps $1\le r\le d$, the target assertion is that eventually the original polynomial

$$
P_n^{(r,d)}(x)=\sum_{k=0}^{\lfloor nr/d\rfloor}a_{n,k}^{(r,d)}x^k
$$

has exactly $\lfloor nr/d\rfloor$ simple negative zeros. The coefficients count labeled binary matrices with equal column sum $k$ and every row sum at most $r$. This is a joint growing-parameter case of Per Alexandersson's open conjecture, which requires real zeros for all sizes. The author states finite rank-two checks and reports a local, unreviewed eventual proof at $U_{2,4}$. Solved-conjectures #165 records bounded screens for the full conjecture. The repository's fixed-parameter theorem allows its cutoff to depend on both $r$ and $d$. [SymCat's statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Original issue #2005](https://github.com/PerAlexandersson/RealRooted/issues/2005) · [Independent investigation #165](https://github.com/1337isnot1337/solved-conjectures/issues/165) · [Repository issue #2](https://github.com/ProgramComputer/open-math-research/issues/2)

The published normalized log-concavity bound already gives a dense subregion. Its exact coefficient-ratio estimate implies eventual separation if $\delta>\log(4)\max_{0\le p\le\rho}p(1-p)$, by minimizing that estimate over internal indices. The simpler global condition $\delta>\log(2)/2$ is a consequence. This method leaves sufficiently small positive $\delta$ uncovered. No external full theorem for the exact joint statement was located. [Normalized log-concavity](https://github.com/ProgramComputer/open-math-research/blob/main/topics/balanced-arrays/orientation-normalization.md)

## Fixed-margin theorem and its use under a cap

Canfield, Greenhill and McKay, *J. Combin. Theory Ser. A* 115 (2008), 32–66, Theorem 1, count $M\times N$ binary matrices of fixed positive integral margins with the same total. For $p$ the common density and $A=p(1-p)/2$, the row deviations must be $O(N^{1/2+\epsilon})$, the column deviations $O(M^{1/2+\epsilon})$, and the aspect conditions are $N=o(A^2M^{1+\epsilon})$ and $M=o(A^2N^{1+\epsilon})$. For constants $a,b>0$ with $a+b<1/2$, the displayed density condition is

$$
\frac{(1-2p)^2}{8A}\left(1+\frac{5M}{6N}+\frac{5N}{6M}\right)\le a\log N.
$$

The theorem assumes $\epsilon>0$ sufficiently small. With $M=n$, $N=d$, column margins all $k$, and $p=k/n$ in a fixed compact subinterval of $(0,1)$, the aspect and density conditions hold uniformly when $d/n$ stays bounded above and below. The central row margins are automatically positive. With $\mu=dk/n$ and $R=\sum_i(s_i-\mu)^2$, the column-deviation sum is zero, giving the following fixed-margin formula.

$$
B(s,(k^d))=\frac{\binom nk^d}{\binom{nd}{dk}}
\left(\prod_i\binom d{s_i}\right)
\exp\left[-\frac12+\frac{R}{2ndp(1-p)}+O(d^{-b})\right].
$$

Use one fixed deviation threshold and fixed density/aspect bounds to control the error uniformly across the admitted margins. [Journal DOI](https://doi.org/10.1016/j.jcta.2007.03.009) · [Author's copy, Theorem 1, internal pp. 2–3](https://web.maths.unsw.edu.au/~csg/papers/CGM.pdf#page=2) · [arXiv v2](https://arxiv.org/abs/math/0606496v2)

The fixed-margin statement alone does not bound the exceptional margins relative to the rare cap event. The following pair argument does.

1. Under the uniform law **on the actual capped labeled arrays** with column sums $k$, fix all rows except a pair $i,j$. In the remaining two entries in each column the residual quota forces $00$ or $11$, or permits a single 1 with either placement. If $a$ columns force $11$ and $b$ columns permit a single 1, the pair's row totals are $a+Y$ and $a+b-Y$, with $Y\sim\mathrm{Bin}(b,1/2)$ restricted by both row caps. This restriction is a central symmetric interval. Thus it can only reduce the tails of $|2Y-b|$. The unrestricted tail is at most $2\exp(-L^2/(2d))$ for a gap of at least $L$, by Hoeffding and $b\le d$. If a row differs from the overall mean by more than $L$, some pair gap is larger than $L$. A union bound gives $n^2\exp(-L^2/(2d))$ as a bound on the exceptional fraction **of the capped arrays**.
2. For the reference margin weights $w(s)=\prod_i\binom d{s_i}$ on $\sum_i s_i=dk$ and $s_i\le r$, conditioning all margins but the same pair gives a hypergeometric law. If that pair has total $h$, sample $h$ positions from $2d$ positions of two colors of size $d$. The row caps restrict the count of one color to a central symmetric interval. Hoeffding for sampling without replacement and $h\le2d$ give a gap tail at most $2\exp(-L^2/(4d))$. This estimate persists up to a uniform constant for the reference weights tilted by $\exp(R/[2ndp(1-p)])$. The pair-dependent part of $R$ after fixing its sum is $(s_i-s_j)^2/2$, so the tilt factor varies by at most $\exp(d/[4np(1-p)])$, bounded in the stated aspect and density ranges. [Hoeffding, §6 and Theorem 4](https://doi.org/10.1080/01621459.1963.10500830)

Taking $L=d^{1/2+\epsilon}$ makes both exceptional fractions superpolynomially small. Sum the uniform fixed-margin theorem over the good margins, and then use the relative tail bounds on both sides to obtain

$$
a_{n,k}^{(r,d)}
=(1+O(d^{-b}))\thinspace
e^{-1/2}\frac{\binom nk^d}{\binom{nd}{dk}}
\sum_{0\le s_i\le r,\thinspace \sum_i s_i=dk}
\prod_i\binom d{s_i}\exp\left(\frac{R}{2ndp(1-p)}\right).
$$

This is uniform for feasible $k$ with $p$ in the chosen compact interval. It allows the cap to be attained, including noninteger $\mu$ and all remainders of $nr$ modulo $d$. The quadratic factor matters at the top. For example, if $n=d$ and $k=r$ then all $s_i=r$, so $R=0$ and the net fixed-margin factor is $e^{-1/2}$. A simple uniform error after removing the factor does not follow from Theorem 1. McKay–Skerman also compare fixed-column graph degree laws with independent binomial margins, but their general expectation rule requires the variable's maximum to be at most polynomially greater than its expectation, a condition that rare cap events can violate. [McKay–Skerman, §1](https://arxiv.org/abs/1302.2446)

For quotas below the cap by much more than $\sqrt{d\log n}$ in row-mean units, elementary concentration covers even $k/n$ near zero. Under independent uniformly chosen $k$-subsets for the columns, one row has law $\mathrm{Bin}(d,k/n)$. The probability of any excess is at most $n\exp(-2(r-\mu)^2/d)$ for $r\ge\mu$, by a union bound and Hoeffding. Consequently $a_{n,k}^{(r,d)}/\binom nk^d=1-o(1)$ uniformly there. The [root-count argument](proof.md) combines the fixed-margin approximation with separate estimates inside the degree range and at the saturated boundary.

## Search record and limits

- Firecrawl and general web searches used `"balanced arrays" "real-rootedness" "uniform matroids" dense`, `"binary matrices" "row sums at most" "real-rootedness" "column sums" polynomials`, and `"dense" "equimarginal" "real-rooted" binary matrices polynomial truncated row margins`. The closest results concern fixed margins and other polynomial invariants.
- The [arXiv Atom search](https://export.arxiv.org/api/query?search_query=all%3A%22balanced%20arrays%22%20AND%20%28all%3A%22uniform%20matroids%22%20OR%20all%3A%22real-rootedness%22%29) returned HTTP 200 and zero metadata hits. Domain searches also used the author and `"dense binary matrices" "degree sequence" random bipartite graphs`. Google Scholar returned a “Verifying…” page for the dense exact-name query. The arXiv metadata index cannot establish absence of an equivalent result in full text.
- GitHub searches included `"balanced arrays" "uniform matroids"`, `("balanced arrays" OR "uniform-matroid balanced-array") "real-rootedness" dense eventual`, issue queries `balanced arrays` in `PerAlexandersson/RealRooted` and `balanced-array` in `1337isnot1337/solved-conjectures`. The author’s and independent issues above were read directly. The X/Twitter domain search combined `"balanced arrays"`, `"equal column sums"`, `"real-rooted"`, and `Alexandersson`. No relevant announcement surfaced. A direct exact-name X search returned HTTP 200 with the generic application shell and no visible posts. [Direct X query](https://x.com/search?q=%22balanced%20arrays%22%20%22uniform%20matroids%22%20%22real-rootedness%22&f=live)

The inspected public evidence does not establish priority against unindexed or unpublished work.
