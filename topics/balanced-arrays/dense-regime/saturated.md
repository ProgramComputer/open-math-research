# Saturated-cap entropy and coefficient curvature

Let $n,d,r$ be integers tending along a sequence with $n\asymp d$ and $r/d$ in a fixed compact subset of $(0,1)$. Set

$$
H(z)=\sum_{i=0}^r\binom di z^i,\qquad
A_k=[z^{dk}]H(z)^n,\qquad
\lambda=d/n,\qquad h=r-dk/n.
$$

The coefficient $A_k$ is the scalar, total-margin model. The conclusions below concern that model. The [main proof](proof.md) transfers the resulting curvature to equal labeled column sums.

For every interior quota $0<k<\lfloor nr/d\rfloor$ with $h=o(\sqrt d)$,

$$
\log\frac{A_k^2}{A_{k-1}A_{k+1}}\ \longrightarrow\ +\infty .
\tag{1}
$$

This applies even when the higher adjacent quota has zero slack. If $h\to\infty$ in this range, the left side is asymptotic to $n\lambda^2/[h(1+h)]$.

## Deficit distribution and variance

Write $a=r/(d-r+1)$ and

$$
H(z)=\binom dr z^r B(a/z),\qquad B(q)=\sum_{j=0}^r c_jq^j,\qquad
c_j=\prod_{i=0}^{j-1}\frac{1-i/r}{1+i/(d-r+1)} .
$$

An empty product is one. Extend $c_j=0$ for $j>r$. Then $c_0=c_1=1$, the $c_j$ are nonincreasing, and

$$
0\ \le\ 1-c_j\ \le\ Cj(j-1)/d
\tag{2}
$$

with a constant uniform in the stated parameter range. For $j\le r$, bound one minus the product by the sum of the deficits of its factors. The deficit of the factor with index $i$ is at most $i/r+i/(d-r+1)$. For $j>r$, the right side in (2) exceeds one for large $d$.

The row deficit $J=r-i$ has tilted law proportional to $c_j q^j$. Its mean $h(q)$ is strictly increasing with $\log q$, with derivative equal to its variance and range $(0,r)$ for $q>0$. For $0<q<1$ let $w=q/(1-q)$. Under the geometric distribution with mean $w$, the multiplicative density adjustment, before its normalization, is $c_J$. Its normalizing expectation is $1+O(w^2/d)$ by (2) and the geometric factorial moments $\mathbb E(J)_p=p!w^p$. For $p=1,2$ and $w=o(\sqrt d)$ one obtains

$$
\mathbb E_q J^p=\mathbb E_{\mathrm{geom}}J^p
+O\left(\frac{w(1+w)^{p+1}}{d}\right).
\tag{3}
$$

Indeed $\mathbb E_{\mathrm{geom}} J^p=O(w(1+w)^{p-1})$ and $\mathbb E_{\mathrm{geom}}[J^p J(J-1)]=O(w(1+w)^{p+1})$ by expanding in falling factorials. Subtract the geometric moment after writing the tilted one as $\mathbb E_{\mathrm{geom}}[c_J J^p]/\mathbb E_{\mathrm{geom}}c_J$.

Because $c_J$ is decreasing, its covariance under the geometric law with $J$ is nonpositive. This follows by taking two independent copies and multiplying their differences. Hence $h(q)\le w$. Given a target $0<h=o(\sqrt d)$, test the geometric parameters of means $h$ and $2h$. The first gives tilted mean at most $h$, and (3) gives tilted mean greater than $h$ at the second, for all sufficiently large $d$. Thus the exact inverse $q=q_h$ lies in $(0,1)$ and its geometric mean lies in $[h,2h]$. Applying (3) again shows

$$
w=h\bigl(1+O((1+h)^2/d)\bigr),\qquad
V=\mathrm{Var}_{q_h}(J)
=h(1+h)\bigl(1+O((1+h)^2/d)\bigr).
\tag{4}
$$

For the variance first subtract the square of the expectation in (3) from the second moment, using that the geometric variance is $w(1+w)$. The bounds are uniform, for example throughout $0<h\le H_d$ for any $H_d=o(\sqrt d)$. At $h=0$ the appropriate tilt is $q=0$, with $V=0$.

## Central mass without a local limit theorem

A log-concave discrete law on an interval of integers with variance $\sigma^2$ and integer mean $M$ satisfies

$$
\frac{c}{1+\sigma}\ \le\ \Pr(X=M)\ \le\ \frac{C}{1+\sigma}
\tag{5}
$$

with numerical positive constants. For the lower bound interpolate $\log \Pr(X=j)$ linearly on the support interval. Concavity and Jensen show that $\log\Pr(X=M)$ is at least minus the discrete entropy. Adding an independent uniform variable on $[-1/2,1/2]$ gives a density whose differential entropy is that discrete entropy and whose variance is $\sigma^2+1/12$. Nonnegativity of relative entropy to the Gaussian of the same mean and variance gives the Gaussian entropy upper bound, implying the left side of (5).

For the upper bound let $b$ be the modal mass, with mode $m$. On either side of the mode let $L$ be the first distance with mass at most $b/2$, extending by zero beyond the support. Since the total mass is one, $L\le 2/b+1\le3/b$. For $j\ge L$, concavity of $\log p_{m+j}$ in $j$ implies $p_{m+j}\le b 2^{-j/L}$, with the same assertion on the other side. If the support already ends, the bound there is immediate. For $0\le j<L$, the bound $p_{m+j}\le 2b\thinspace 2^{-j/L}$ is immediate from the modal mass. Consequently both sides are bounded by $2b\thinspace 2^{-bj/3}$. Summing $j^2$ against this bound gives $\sigma^2\le\mathbb E(X-m)^2\le C'/b^2$, using, for example, the differentiated geometric series. Since also $b\le1$, this proves the upper bound.

The deficit law proportional to $c_jq^j$ is log-concave because its successive nonzero coefficient ratios decrease, as seen in the product formula. Its $n$-fold convolution is also log-concave with interval support. One elementary proof uses the Toeplitz matrix of a sequence extended by zero to the integers. Interval support and the decreasing ratio condition imply that its $2\times2$ minors are nonnegative, by comparing products of two terms with the same index sum. Toeplitz matrix multiplication gives convolution, and Cauchy–Binet shows that these minors remain nonnegative. The sums in that formula are finite for the finite supports here. Adjacent $2\times2$ minors give log-concavity.

Define the deficit entropy

$$
g(h)=\log B(q_h)-h\log q_h,\quad g(0)=0 .
$$

For $\ell=nh=nr-dk$ an integer in range, independent tilted deficits give the exact equality

$$
A_k=\binom{d}{r}^{n} a^\ell e^{ng(h)}
\Pr(J_1+\cdots+J_n=\ell).
\tag{6}
$$

The total mean equals $\ell$ and its variance is $nV$. Combining (4) and (5) gives

$$
\log A_k=n\log\binom dr+\ell\log a+ng(h)
-\tfrac12\log(1+n h(1+h))+O(1)
\tag{7}
$$

uniformly for $0\le h=o(\sqrt d)$, with exact prefactor one at $h=0$. Thus no local limit theorem is required even when $nV$ is bounded. For an optional sharper description when $\ell$ is fixed, the coefficient of $q^\ell$ in $B(q)^n$ is $n^\ell/\ell!+O_\ell(n^{\ell-1})$ for $\ell\ge1$, because using exactly $\ell$ factors of degree one gives $\binom n\ell$ and every other allocation uses at most $\ell-1$ nonconstant factors. For $\ell=0$ it is one. Equivalently, for fixed $\ell$ the probability factor in (6) tends to $e^{-\ell}\ell^\ell/\ell!$, interpreted as one at zero, using $q_h\sim \ell/n$, $B(q_h)=1+q_h+O(q_h^2)$ when $\ell>0$.

## Curvature and the floor maximum

Differentiation at positive slack gives

$$
g'(h)=-\log q_h,\qquad g''(h)=-1/V.
\tag{8}
$$

The entropy extends continuously to $h=0$, since $q_h\sim h$ near zero. For $h\to\infty$ with $h=o(\sqrt d)$, the three variance scales in (7) at $h-\lambda,h,h+\lambda$ are comparable. Thus the logarithmic prefactors contribute $O(1)$ to the centered second difference. Using (8) and the triangular integral for a second difference gives

$$
2g(h)-g(h-\lambda)-g(h+\lambda)
=\int_{-\lambda}^{\lambda}\frac{\lambda-|u|}{V(h+u)}\thinspace du
\sim\frac{\lambda^2}{h(1+h)} .
$$

The expression times $n$ tends to infinity, so (7) proves the stated asymptotic in (1) for $h\to\infty$.

For bounded $h$ at an interior quota with $h-\lambda\ge0$, the logarithmic prefactors give only $O(\log n)$. The triangular integral still supplies a positive lower bound independent of $d$ by restricting it to the central interval $|u|\le\lambda/2$, using $V(h+u)\le C$ there by (4). The same lower bound applies when $h-\lambda=0$, by continuity and concavity, or by taking a limit of second differences from centers above $h$. It follows that (1) is at least $c n-O(\log n)$ in each bounded-slack range. These alternatives also imply (1) for sequences with oscillating slack by subsequences.
