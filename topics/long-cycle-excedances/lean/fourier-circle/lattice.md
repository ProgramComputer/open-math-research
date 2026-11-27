# The consecutive-row pole product on the odd lattice

Let $s$ be real, $r=\sqrt{s^2+\pi^2}$ and $R>0$. For $\ell\in\mathbb Z$ put $m_\ell=2\ell+1$ and $p_\ell=s+i m_\ell\pi$. Assume $R\ne|p_\ell|$ for every $\ell$. For an integer $k\ge3$ define

$$
c_\ell=R^k/p_\ell^{k-1},\qquad
a_\ell=\frac{|c_\ell|}{\sqrt{\bigl||p_\ell|^2-R^2\bigr|}},\qquad
C=s/r,\qquad S=\pi/r.
$$

The Lean theorem uses the unnormalized angular measure. With $w=Re^{ix}$ it gives

$$
\int_0^{2\pi}\left|\left(\sum_\ell\frac{c_\ell}{p_\ell-w}\right)
\left(\sum_\ell\frac{(r/p_\ell-C)c_\ell}{p_\ell-w}\right)\right|\mathop{}\mathrm{d}x
\le 2\pi S\left(\sum_\ell a_\ell\right)\left(\sum_\ell |m_\ell|a_\ell\right).
$$

Both sums on the right converge absolutely for every $k\ge3$. For all but finitely many poles $|p_\ell|\ge2R$, so the inverse square root in $a_\ell$ is at most $2/|p_\ell|$. The inequality $|m_\ell|\le |p_\ell|$ bounds the first weighted moment by a constant times the absolutely convergent series of reciprocal powers with exponent $k-1$. The proof includes both tails of the integer lattice. [Absolute convergence](FourierLatticeWeights.lean) · [Reindexing the full lattice](FourierOddPoleProduct.lean)

For $z=C+i mS$ with $C^2+S^2=1$ and $|m|\ge1$, the contrast satisfies $|1/z-C|\le|m|S$. After squaring and multiplying by $|z|^2$, the difference between the right and left sides is $S^4(m^4-1)$. Applying this estimate at $z=p_\ell/r$ supplies the contrast factor for the original locations and residues. [Geometric inequality](FourierPoleContrast.lean) · [Literal lattice theorem](FourierRowPoleProduct.lean)

The proof checks the product term in the two Fourier integrations. The derivative of the weighted kernel adds a sum of squared-pole terms. The generating-function derivative identity, quantitative weight bounds and outer row normalization are further obligations in the large-aspect proof. [Common-circle argument](../../fourier-circle/README.md) · [Fourier verification and build command](README.md)

On the shared Lean 4.19.0 research pin, all thirteen Fourier modules compiled in a fresh module directory and the 24 named axiom reports contained only `propext`, `Classical.choice` and `Quot.sound`. The local check rebuilt the six missing upstream mathlib imports directly from their pinned Git sources. The [checker](check.py) includes the signed lattice, both moment series, the geometric contrast and the literal pole-product theorem.
