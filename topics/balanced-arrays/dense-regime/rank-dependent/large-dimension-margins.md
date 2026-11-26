# Variance-scale margin averaging in the polynomially sparse range

Let $\epsilon>0$ and $c>0$ be fixed. Suppose that
$d\ge n^{3/4+\epsilon}$, $d\le n$, and the quota $i$ satisfies
$p=i/n\to0$ and $p\ge c d/n$. Write $\mu=dp$, and allow any cap
$r\ge\mu$. Put

$$
H(z)=\sum_{s=0}^r\binom ds z^s,\qquad
A_i=[z^{di}]H(z)^n,\qquad
K_i=\frac{\binom ni^d}{\binom{nd}{di}}.
$$

For $\mu<r$ let $S$ be the scalar tilted law proportional to
$\binom ds z^s$ on $0\le s\le r$ with mean $\mu$, and write
$V=\mathrm{Var}(S)$. At $\mu=r$ take the deterministic law. Then
for some fixed $\beta>0$ the capped labeled count satisfies

$$
a_i=K_i A_i\exp\left(-\frac12+\frac{V}{2\mu(1-p)}
+O(n^{-\beta})\right).
\tag{1}
$$

The estimate is uniform under the stated bounds along sequences,
including exactly saturated quotas. No upper bound on $r/\mu$
is used.

## Actual and scalar row tails

Fix one labeled row of an actual uniformly chosen capped array. If
its occupied set is any $s$-subset of the columns, let $B_s$ count
completions on the remaining $n-1$ rows. These are precisely the
arrays with $s$ designated quotas $i-1$ and all other quotas $i$,
and the count depends only on $s$. Deletions give interval positive
support in $s$, and the mixed orientation inequality applied at
the vector with $s+2$ reduced quotas gives $B_sB_{s+2}\le B_{s+1}^2$.
The actual mass at $s$ for $0\le s\le r$ is

$$
\mathbb P(S_{\mathrm{actual}}=s)=\frac{\binom ds B_s}{a_i},
$$

and it is zero for $s>r$. This mass has log-concave likelihood ratio relative to
$\mathrm{Bin}(d,p)$. Its mean is $\mu$ by row symmetry. The scalar
tilted law has a geometric likelihood ratio through the cap and
the same mean. [Mixed orientation inequality](../../orientation-normalization.md#extension-across-two-coordinates)

An interval superlevel set at one for the likelihood ratio and equal
means imply convex domination by the reference binomial. Indeed,
subtract from a convex function the affine secant across that
interval, choosing endpoints between lattice sites. The residual
is nonpositive inside and nonnegative outside, so its sum against
the signed difference of the masses is nonpositive. The affine
part cancels. A point mass is covered directly by Jensen.
In particular $V\le\mu(1-p)$, and binomial exponential moment
bounds imply, in either row law, the Bernstein tail

$$
\mathbb P(|S-\mu|>y)\le 2\exp(-c_1 y^2/(\mu+y)).
\tag{2}
$$

For a fixed sufficiently small $\eta>0$ put $W=\mu^{1/2+\eta}$,
which is $o(\mu)$. The exceptional row profiles have relative
mass at most $2n\exp(-c_2\mu^{2\eta})$ in the actual counting
measure by the union bound, and the same bound under independent
scalar rows, before conditioning. Since
$\mu\ge c d^2/n\ge c n^{1/2+2\epsilon}$, these bounds decay faster
than any inverse power of $n$.

## Published fixed-margin hypotheses

Apply Theorem 1.1 of the published Liebenau–Wormald paper with
part sizes $n,d$, edge count $pnd$, row average $\mu$, and column
average $i$. Its small-density condition holds since $p\to0$.
Take $0<\eta<\kappa<1/10$ with $\kappa$ sufficiently small in
terms of $\epsilon$. The regular row deviations are
$W=o(\mu^{1/2+\kappa})$, and the column deviations vanish.
The left-hand growth term divided by the right-hand scale in
their equation (3) is

$$
\mathcal A=
\left(\frac{n}{d^{3/2-5\kappa}}+\frac{d}{n^{3/2-5\kappa}}\right)
p^{5\kappa-1/2}
\le C\frac{n^{3/2-5\kappa}}{d^{2-10\kappa}}
=O(n^{-\gamma})
$$

for some $\gamma>0$. Here $p\ge cd/n$ and $5\kappa-1/2<0$,
and the exponent at $d=n^{3/4+\epsilon}$ is
$-2\epsilon+\kappa(5/2+10\epsilon)<0$. Equation (4) follows
from $(\log^K d/d+\log^K n/n)/p=O(n\log^K n/d^2)$ for every
fixed $K$. The error in equation (5) is
$O(\log^2 n/\sqrt n+\log^2 d/\sqrt d+\mathcal A)$, giving a
polynomial saving. With zero column variance, Remark 1.2
then gives the regular profile count

$$
K_i\prod_j\binom d{s_j}
\exp\left(-\frac12+\frac{\sum_j(s_j-\mu)^2}{2n\mu(1-p)}
+O(n^{-\beta_0})\right)
\tag{3}
$$

for some $\beta_0>0$. [Published Theorem 1.1, equations (3)–(5) and Remark 1.2](https://onlinelibrary.wiley.com/doi/full/10.1002/rsa.21105#rsa21105-mthst-0001)

## Averaging the exponential correction without a global Gaussian tail

Let $Y=(S-\mu)^2/\mu$. Rare large deviations cannot be controlled
by asserting a uniform exponential moment at a fixed positive
argument. The actual required small arguments can be controlled
directly from (2). Indeed

$$
\mathbb P(Y>v)\le 2\exp\left(-\frac{c_1v}{1+\sqrt{v/\mu}}\right).
\tag{4}
$$

On the support $v\le d^2/\mu$, so
$1+\sqrt{v/\mu}\le1+1/p\le2/p$. For $0\le t\le c_1p/4$, the factor
$e^{tv}$ consumes at most half the exponent in (4). Moreover

$$
\frac{v}{1+\sqrt{v/\mu}}\ge \frac12\min(v,\sqrt v)
$$

since $\mu\ge1$ for large $n$. Integrating (4) against the derivative
of $v^2 e^{tv}$ now gives a numerical bound for
$\mathbb E[Y^2 e^{tY}]$ on that range. The bound at $t=0$ also suffices
for negative $t$. Hence

$$
\log\mathbb E e^{tY}=t\mathbb E Y+O(t^2)
\qquad (|t|\le c_1p/4)
\tag{5}
$$

uniformly. This argument uses only the universal row support bound
$|S-\mu|\le d$.

Let $Q=n^{-1}\sum_{j=1}^nY_j$ for independent tilted rows.
Because $p\ge c n^{-1/4+\epsilon}$, the arguments of order
$n^{-1/3}$ needed in exponential Markov fall in (5). With
$c_p=1/[2(1-p)]$ it follows that

$$
\mathbb P(|Q-\mathbb EY|>n^{-1/3})\le2e^{-c_3 n^{1/3}},
\qquad
\mathbb E e^{2c_p Q}=\exp(2c_p \mathbb E Y+O(n^{-1}))=O(1).
$$

For the second bound use independence and (5) at $2c_p/n$,
and $\mathbb E Y=V/\mu\le1-p$.

The profile weights proportional to $\prod_j\binom d{s_j}$ at total
$di$ are exactly the independent scalar row law conditioned on that
total. Its probability is at least $1/(nd+1)$, since the sum is
log-concave on an integer interval, and Jensen on the interpolated
log mass at the mean bounds it below by the exponential of minus
the entropy. The entropy is at most $\log(nd+1)$. Cauchy–Schwarz with
the bounded weighted moment above makes both the exceptional row
event and the exceptional $Q$ event negligible to every power of
$n$ in the weighted conditional average. On the complement
$e^{c_p Q}=e^{V/[2\mu(1-p)]}(1+O(n^{-1/3}))$. Sum (3) and use
the actual relative row tail bound. This proves (1).
