# Differentiating an infinite pole sum on a circle

Let $R>0$, let $w=Re^{ix}$, and let $p_j$ be a sequence of poles whose moduli differ from $R$, with $|p_j|\ge2R$ for all but finitely many indices. Define

$$
D(x)=\sum_j\frac{c_j}{p_j-w},\qquad
K_j=\frac{1}{\sqrt{\bigl||p_j|^2-R^2\bigr|}}.
$$

Assume both series of nonnegative weights $\sum_j|c_j|K_j$ and $\sum_j|c_j|K_j^2$ converge. Then

$$
D'(x)=iw\sum_j\frac{c_j}{(p_j-w)^2},\qquad
\int_0^{2\pi}|D'(x)|\mathop{}\mathrm{d}x\le 2\pi R\sum_j|c_j|K_j^2.
$$

For a single pole the squared distance kernel has angular mean $K_j^2$. The nonnegative sum retains the exact weighted mean by dominated convergence. The angular derivatives of the complex summands have a summable bound independent of the angle, and the undifferentiated series converges absolutely at zero. These facts justify differentiating the complex series before estimating the norm. [Positive squared-pole sum](FourierSquaredSum.lean) · [Termwise derivative](FourierPoleDifferentiation.lean) · [Integrated bound](FourierDerivativeBound.lean)

The two choices of residues in the common-circle argument give the old-row and contrast derivative terms once the corresponding squared weights are controlled. The identity between the original generating-function derivative and its odd-pole expansion is a separate obligation. [Fourier proof and reproduction command](README.md)

On the shared Lean 4.19.0 research pin the 16 modules compiled in a fresh module directory. The 28 named axiom reports passed using only `propext`, `Classical.choice` and `Quot.sound`. [Reproduction commands](README.md)

The pinned Linux build at `fb71999af06ecf678c4bbcca9e1a7d9bcf0d2607` matched all 16 Git source hashes and passed the 28 named axiom audits. An independent agent checked the positive derivative sign, the radius factor from the angular velocity and cancellation of $2\pi$ under normalized angular measure. The reviewer identified $R T_0$ and $R S T_1$ as the two applications when their squared weights are supplied. [Hosted verification](https://github.com/ProgramComputer/open-math-research/actions/runs/46003560740)
