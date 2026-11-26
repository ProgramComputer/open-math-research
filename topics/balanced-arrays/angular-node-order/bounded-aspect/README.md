# Angular signs at interior quotas and bounded aspect

Let $P_n(q)=\sum_m a_m q^m$, where $a_m$ counts labeled $n\times d$ binary arrays with common column sum $m$ and row sums at most $r$. For $n\ge d\ge2$, $1\le r<d$, and $1\le k<\lfloor nr/d\rfloor$, let $w_k$ be the positive tilt satisfying $\Psi(w_k)=k\pi$. The sign tested below is the sign at the exact angular radius $w_k^d$. [Angular phase and ordering](../README.md)

## Eventual sign on compact interior density intervals

**Theorem.** For each $0<\varepsilon<1/2$ and $1\le K<\infty$, there is an $N(\varepsilon,K)$ such that for every $n\ge N(\varepsilon,K)$ with $1\le n/d\le K$, the exact angular node satisfies

$$
(-1)^k P_n(-w_k^d)>0
$$

uniformly over the proper caps $r$ and all internal quotas with $k/n\in[\varepsilon,1-\varepsilon]$. The height cutoff is existential. The cap may vary with $n,d$ and the tested quota may lie a bounded distance from saturation.

The proof extends the adjacent coefficient comparison to every compact interior density interval. When the tilted row variance is proportional to dimension, the angular tilt cancels the linear coefficient drift and the signed local sum tends to a positive Jacobi product. In the other variance regimes the neighboring terms vanish relative to the central term. [Proof](bounded-aspect-angular-signs.md) · [Independent review](bounded-aspect-angular-review.md)

## Explicit finite sign when overflow is rare

**Lemma.** Suppose $n\ge10^6$, $3\le n/d\le4$, $1/4\le k/n\le3/4$, and

$$
\frac rd-\frac{k+3}{n}\ge\sqrt{\frac{2\log n}{d}}.
$$

Then $(-1)^k P_n(-w_k^d)>0$ at that quota. A binomial phase bracket locates the true node. The seven terms centered at quota $k$ give a strictly positive signed contribution, and log-concavity controls the omitted tails. [Proof and constants](finite-rare-overflow-angular.md) · [Independent review and rational replay](finite-rare-overflow-review.md)

Coefficient ratios give a quantitative order at mixed angular and geometric interfaces. Exact examples record the limits of the prior finite sign tests. [Mixed angular and geometric test radii](interface/README.md)

**Formal verification**　⬜ None. Both arguments have independent agent-assisted reviews.
