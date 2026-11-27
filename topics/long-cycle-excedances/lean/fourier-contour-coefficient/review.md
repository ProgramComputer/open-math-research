# Independent contour-transfer scope review

Agent-assisted review by the discrete pole-moment verifier on November 27, 2026.

I read the exact `d99561826d76d48700eb16a871d0b022c5e56644` source, including the literal adapter, Fourier normalization, analytic small-circle extraction, absolute pole-series expansion, pole removal and annular transfer. This is a source-only review. The displayed coefficient and signed adjacent identities match the source.

The defining Fourier mode is $\exp(-in\theta)$, averaged by $1/(2\pi)$ on $[0,2\pi]$. The counterclockwise circle derivative is $iw$, so the factor for $\int f(w)w^{-(n+1)}\,dw$ is $2\pi i/R^n$ times the normalized angular coefficient.

At a logistic pole $p$, the derivative of the denominator is $-1$, so the principal-part coefficient of $f(w)/w^{n+1}$ is $-T(p)/p^{n+1}$. The annular theorem uses outer minus inner equal to $2\pi i$ times the sum of these coefficients. Solving for the inner Taylor coefficient therefore gives the positive sign for the displayed residue contributions. The code excludes poles on the outer boundary and chooses an inner radius strictly below every pole.

On the small disk the double series is dominated on the product index set by $(|w|/\pi)^m\,|w|/|P_l|^2$. The geometric factor sums and the inverse-square pole series sums, so the exchange of degree and pole order is absolute. The anchored resolvent contributes degrees $m+1$ with denominators $P_l^{m+2}$. Degree zero uses the exact constant logistic coefficient $1/(1-t)$. The entire finite tilt has an absolutely summable Taylor expansion, and the Cauchy product uses the original logistic coefficient identity, giving $E_{n,k}(t)/((1-t)^{n+1}n!)$. This uses the literal enumerator at one parameter $t=-e^{-s}$, including $s=0$.

The adjacent theorem applies the two coefficient formulas at $n$ and $n+1$ with the same contour, pole set, cutoff and parameter. Factoring out $R^{-n}$ gives the multiplier $r/R$ for the new Fourier coefficient. Factoring $p^{-(n+1)}$ gives $(r/p-C)$ for each residue. The theorem holds independently of whether the old row vanishes. Its scope is an identity and leaves the boundary and enclosed-residue bounds to the linked components.
