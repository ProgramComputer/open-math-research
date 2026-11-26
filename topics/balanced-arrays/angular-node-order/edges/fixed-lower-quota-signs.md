# Signs at a fixed lower quota in large dimension

Fix an integer $k\ge1$. For integers $n\ge d\ge2$ and $1\le r<d$, let $a_m$ count labeled $n\times d$ binary arrays with common column sum $m$ and row sums at most $r$. Put $D=\lfloor nr/d\rfloor$ and $P(q)=\sum_{m=0}^D a_m q^m$. For $k<D$, let $w_k$ be the unique positive solution of $\Psi(w_k)=k\pi$, and set $T_m=a_m w_k^{dm}$. [Exact angular phase and node ordering](../README.md)

**Theorem.** Put $\delta_k=1/(2k+3)$ and

$$
\rho_k=\max\left\lbrace
\frac{k}{k+\delta_k},\quad
\frac{2k(k+\delta_k)}{(k+1)(2(k+\delta_k)-1)},\quad
\frac{k+1/2}{k+1}
\right\rbrace<1.
$$

For every $\eta\in(\rho_k,1)$ there is a dimension threshold $d_0(k,\eta)$ such that for every $d\ge d_0(k,\eta)$, uniformly over $n\ge d$ and $1\le r<d$ with $k<D$,

$$
\frac{\max(T_{k-1},T_{k+1})}{T_k}\le\eta^d,
\qquad
\left|\frac{(-1)^kP(-w_k^d)}{T_k}-1\right|
\le\frac{2\eta^d}{1-\eta^d}.
$$

The term at quota $k$ determines the sign at the true angular node once $d$ is sufficiently large. In particular $(-1)^kP(-w_k^d)>0$ then holds at every admissible height and proper cap for this fixed $k$. The dimension threshold is existential.

**Corollary.** For each fixed $k\ge1$, only finitely many triples $(n,d,r)$ with $n\ge d\ge2$, $1\le r<d$, and $k<\lfloor nr/d\rfloor$ can fail the strict sign at that node. The theorem leaves finitely many dimensions to check. In each of those dimensions, the fixed-dimension all-quota theorem gives all internal signs for every sufficiently large $n$, uniformly over the proper caps. [Fixed-dimension theorem](all-quota-signs.md)

**Formal verification**　⬜ None. The written argument has an independent agent-assisted review. [Review and detailed derivation](fixed-quota-node-review.md)

## Proof outline

For a sequence with $n/d\to\lambda<\infty$, pass to a subsequence on which the cap has limit $R$, allowing $R=\infty$. The node equation traps $dw_k$ in a compact positive interval. At a limit $x$, the capped Poisson mean $\mu(x)$ satisfies $\lambda\mu(x)=k+x\mu'(x)/(2\mu(x))$. To find the exponential scale of $T_m$ for each fixed neighboring quota $m$, allocate $dm$ labeled stubs, $m$ from each column, into rows. For a fixed finite cap the expected number of same-column collisions is bounded. Repairing collisions by swaps loses at most a polynomial factor in the count. A coefficient estimate for the capped Poisson row series then gives the exponential rates. Fixed finite caps and the unrestricted model bound the case $R=\infty$.

Concavity of the capped Poisson mean and a binomial-mixture variance bound give the first two constants in $\rho_k$ for the left and right neighboring terms. When $n/d\to\infty$, the phase instead gives $nw_k\to k+1/2$. The disjoint-column count and the unrestricted count give the third constant as a bound for both neighboring rates. Every unbounded dimension sequence has a subsequence in one of these regimes, which makes the adjacent-term bound uniform.

Normalized log-concavity of the array counts implies ordinary log-concavity of $(T_m)$. Each side of $T_k$ is therefore bounded by a geometric sequence with ratio at most $\eta^d$. Summing those two sequences gives the stated relative error. [Normalized log-concavity](../../orientation-normalization.md) · [Detailed estimates, including endpoint neighbors](fixed-quota-node-review.md)
