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

Only finitely many pairs $(d,k)$ can fail strict positivity of this
limiting value. The proof gives no explicit finite cutoff and leaves
open whether any exceptional pairs exist.
[Lower limit](phase-edge-transfer.md#lower-edge) · [Finiteness proof](phase-edge-review.md#positive-lower-signs-for-growing-dimension)

**Formal verification**　⬜ None. The upper sign and both transfer
arguments underwent one independent agent-assisted review. A second
agent independently reviewed the lower limiting sign finiteness proof.
[Upper and transfer review](phase-edge-review.md#upper-sign-and-transfer) · [Lower finiteness review](phase-lower-review.md)

These are fixed-edge results as the height grows. Establishing the
prescribed signs at every angular test radius for every admissible
height remains open.
