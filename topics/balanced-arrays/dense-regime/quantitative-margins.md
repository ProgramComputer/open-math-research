# Appendix. Quantitative summation over row margins

Let $a_K$ count capped balanced arrays with $n$ rows, $d$ columns, row cap $r$, and common column sum $K$. Put $D=\lfloor nr/d\rfloor$, $\delta=d/n$, $p=K/n$, and $u=p(1-p)$. Set

$$
G(z)=\sum_{s=0}^r\binom ds z^s,\qquad U_K=[z^{dK}]G(z)^n.
$$

For $0<dp<r$ let $S$ have probabilities proportional to $\binom ds z^s$ on $0\le s\le r$, with $z>0$ chosen so that $\mathbb E S=dp$. The mean increases strictly with $\log z$, with derivative $\mathrm{Var}(S)$, so the tilt is unique. At exact saturation use $S=r$. Write $v_K=\mathrm{Var}(S)/d$.

## Relative coefficient estimate

Assume $\delta\le C_0$ and $\delta\log n\to\infty$. Let $k$ be an internal quota satisfying $a_k^2/(a_{k-1}a_{k+1})\le4$. Fix $J\ge0$ and consider the available quotas $|K-k|\le(\log n)^J$. Let $W/\sqrt{d\log n}\to\infty$. Suppose a fixed-margin estimate, uniform over these quotas and all row profiles $\mathbf s$ with $\sum_i s_i=dK$, $0\le s_i\le r$ and $\max_i|s_i-dp|\le W$, gives the count with profile $\mathbf s$ and all column sums $K$ as

$$
\frac{\binom nK^d}{\binom{nd}{dK}}\prod_{i=1}^n\binom d{s_i}
\exp\left(-\frac12+\frac{V(\mathbf s)}{2u}+O(E_n)\right),
\qquad
V(\mathbf s)=\frac{1}{nd}\sum_{i=1}^n(s_i-dp)^2,
\tag{A.1}
$$

where $E_n=o(1)$. Then, uniformly throughout the window,

$$
a_K=\frac{\binom nK^d}{\binom{nd}{dK}} U_K
\exp\left(-\frac12+\frac{v_K}{2u}\right)
\left(1+O\left(E_n+\frac{n^{-1/3}}{\delta}\right)\right).
\tag{A.2}
$$

The hypothesis concerns the profile formula and its uniform error. A different fixed-margin theorem, including a Liebenau–Wormald formula reduced to (A.1) in the equal-column case, can supply it.

**Proof.** The normalized log-concavity inequality bounds the ratio at $k$ below by $(1+(n+1)/(k(n-k)))^d$. Using $\log(1+x)>x/(1+x)$ shows that uniformly in the window,

$$
u\ge \frac{\delta}{\log4}-O\left(\frac{1+(\log n)^J}{n}\right)
=\frac{(1-o(1))\delta}{\log4}.
\tag{A.3}
$$

For an actual array chosen uniformly, condition on all but two rows. If $b$ columns require one entry in the pair, its row-size difference has the law of $2Y-b$, where $Y$ is binomial $(b,1/2)$ conditioned on the central symmetric interval imposed by the caps. Columns requiring two ones contribute equally to the rows. The conditioning can only decrease the absolute gap, whose tail at $W$ is at most $2e^{-W^2/(2d)}$ by the binomial bound. A deviation greater than $W$ from the mean $dp$ requires a pair with gap greater than $W$. Thus the irregular actual profiles have relative mass at most $2n^2e^{-W^2/(2d)}$, smaller than every negative power of $n$.

The candidate law of $S$ is dominated in convex order by the binomial law with parameters $(d,p)$. The ratio of their masses is geometric through the cap and zero above it, so the set where the first mass exceeds the second is an interval. For a convex test function subtract an affine secant across this interval, with endpoints between lattice sites. The residual is nonpositive inside and nonnegative outside. Equal mass and mean cancel the secant and give convex dominance. Identical and point-mass cases obey the comparison directly. In particular $v_K\le u$, and exponential moments give the binomial sub-Gaussian tail for $(S-dp)/\sqrt d$.

Let $\mathcal E=\lbrace\sum_iS_i=dK\rbrace$ for independent copies of the candidate row. The sum has log-concave mass function $f$ with contiguous support. Indeed adjacent ratio comparison gives nonnegative order-two minors for the Toeplitz matrix of each mass function, and convolution preserves these minors by Cauchy–Binet. Jensen's inequality for the piecewise-linear concave interpolation of $\log f$ at the integer mean gives $\log\Pr(\mathcal E)\ge\mathbb E\log f(\sum_iS_i)\ge-\log(nd+1)$. The latter inequality is the entropy bound on this finite support. These statements also hold for a point mass.

Write $Y_i=(S_i-dp)/\sqrt d$, $V=n^{-1}\sum_iY_i^2$ and $C=1/(2u)$. The uniform exponential moment of $Y_i^2$ gives $\log\mathbb E e^{tY_i^2}=tv_K+O(t^2)$ near zero. Exponential Markov bounds give

$$
\Pr(|V-v_K|>n^{-1/3})\le 2e^{-c'n^{1/3}},
\qquad
\mathbb E e^{2CV}=\exp(2Cv_K+O(C^2/n))=O(1).
$$

Here $C=O(\delta^{-1})=O(\log n)$ and $v_K\le u$. By Cauchy–Schwarz and the lower bound on $\Pr(\mathcal E)$, the conditional $e^{CV}$-weighted contribution of either the deviation event or irregular candidate profiles is smaller than every negative power of $n$. On the complementary event the weight is $e^{Cv_K}(1+O(Cn^{-1/3}))$. Given $\mathcal E$, the profile probabilities are proportional to $\prod_i\binom d{s_i}$ and sum to one with normalizer $U_K$. Summing (A.1) and applying the actual relative tail bound gives (A.2). At exact saturation both the row law and the conditioned profile are deterministic. $\square$

## Range supplied by Canfield–Greenhill–McKay

Canfield–Greenhill–McKay, Theorem 1, uses $A=u/2$ and constants $a,b>0$ with $a+b<1/2$. For one sufficiently small fixed $\epsilon>0$, it allows uniform row deviations $O(d^{1/2+\epsilon})$, zero column deviations, and the size conditions $d=o(A^2n^{1+\epsilon})$ and $n=o(A^2d^{1+\epsilon})$. The density condition in the present row and column notation is

$$
\frac{(1-2p)^2}{4u}
\left(1+\frac{5}{6\delta}+\frac{5\delta}{6}\right)
\le a\log d.
\tag{A.4}
$$

Under these conditions the theorem gives (A.1) with $E_n=d^{-b}$. Profiles in the application have positive row and column margins for sufficiently large $n$. The theorem is applied with fixed $a,b,\epsilon$ and a unit bound on the normalized row deviations, so its asymptotic error is uniform over the admissible profiles. Equivalently, a sequence violating any proposed uniform bound could be chosen from the same family and would satisfy the same fixed hypotheses. [Canfield, Greenhill and McKay, JCTA 115 (2008), 32–66](https://doi.org/10.1016/j.jcta.2007.03.009) · [Authors’ manuscript, §1, Theorem 1](https://web.maths.unsw.edu.au/~csg/papers/CGM.pdf#page=2)

When $p$ stays in a fixed compact subinterval of $(0,1)$, $\delta\log n\to\infty$ makes the left side of (A.4) $o(\log d)$. Thus CGM supplies the full relative estimate there. At potentially noncompact densities, (A.3) makes the left side at most $(5\log4+o(1))/(24\delta^2)$ when $\delta\to0$. Consequently CGM also supplies the estimate throughout the quota window whenever

$$
\delta\ge \frac{c}{\sqrt{\log n}},\qquad c>\sqrt{\frac{5\log4}{12}}.
$$

Choose $5\log4/(24c^2)<a<1/2$ and $0<b<1/2-a$. The sizes and the regularity width $W=d^{1/2+\epsilon}$ satisfy the preceding hypotheses in both ranges, since $d$ and $A^{-1}$ differ from $n$ and $1$ by at most logarithmic factors in the required directions. At $c=1$, $a=1/3$ and $b=1/10$ are valid. The [fixed-margin enumeration](sparse-enumeration.md) supplies the required estimate at all densities in the sublinear range $\delta\to0$ and $\delta\log n\to\infty$.
