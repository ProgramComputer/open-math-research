# Edge signs at the ordered angular test points

Fix an integer dimension $d\ge2$ and a proper uniform row cap $1\le r<d$.
Let $P(q)=\sum_k a_k q^k$, where $a_k$ counts labeled binary arrays with
$n$ rows, all $d$ column sums equal to $k$, and all row sums at most $r$.
Write $D=\lfloor nr/d\rfloor$. The angular test radius $w_k^d$ is
defined by the phase equation $\Psi(w_k)=k\pi$. The ordering theorem
gives uniqueness for $n\ge d$ and $1\le k<D$.
[Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Angular node ordering](https://github.com/ProgramComputer/open-math-research/blob/b37c6be08b892ba4d2bd8a58fb6b2c491438d37a/topics/balanced-arrays/angular-node-order/README.md)

**Upper edge.** For every fixed integer $j\ge1$, the actual polynomial
satisfies $(-1)^{D-j}P(-w_{D-j}^d)>0$ for all sufficiently large $n$
with $d,r,j$ fixed. The proof covers each residue of $nr$ modulo $d$.
Its limiting factorial sections have the required strict sign for
every $d\ge2$, every $j\ge1$, and every residue $0\le s<d$.
[Upper limiting signs](angular-upper-edge-sign.md) · [Transfer to actual radii](phase-edge-transfer.md#upper-edge)

**Lower edge.** At each fixed $k\ge1$, put $\theta=\pi/d$ and
$U_{d,k}=(\theta/\sin\theta)(k+(d-1)/(2d))$. The actual signed
polynomial value at the angular radius converges to

$$
(-1)^k F_d(-U_{d,k}^d),\qquad F_d(q)=\sum_{m\ge0}\frac{q^m}{(m!)^d}.
$$

The limiting value is strictly positive for every integer $d\ge2$
and $k\ge1$. The gamma-mixture proof reduces the question to
15,751 pairs, which both independent checkers certify. Thus for
each fixed lower quota the actual polynomial has the prescribed sign
once the row count is sufficiently large with $d,r,k$ fixed.
[Lower limit](phase-edge-transfer.md#lower-edge) · [Gamma-mixture proof](lower-gamma-mixture.md) · [Finite certificate and replay](lower-finite-certificate.md)

**All internal quotas at fixed dimension.** For every $d\ge2$ there
is an $N(d)$ such that for $n\ge N(d)$, simultaneously for all
$1\le r<d$, the prescribed signs hold at every internal angular
test radius. The cutoff is existential. For $d=2$ the signs hold
at every admissible height. The all-height sign problem
remains open.
[All-quota proof](all-quota-signs.md)

**Formal verification**　⬜ None. The upper sign and both transfers
had an independent agent-assisted review, as did the earlier lower
finiteness proof. The gamma-mixture reduction and all-quota result
have separate agent-assisted reviews.
[Upper and transfer review](phase-edge-review.md#upper-sign-and-transfer) · [Earlier lower finiteness review](phase-lower-review.md) · [Gamma-mixture review](lower-gamma-review.md) · [All-quota review](lower-all-quota-review.md)

A direct finite-array analogue obtained by averaging dilations of the unshifted total-load section on the unit interval fails already at four rows and four columns. The same obstruction holds for an infinite family of high row caps. [Counts, proof and review scope](finite-section-obstruction.md)
