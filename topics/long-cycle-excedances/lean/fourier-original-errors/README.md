# Boundary coefficients of the original permutation trace

Let $k\ge100$, $x=n/k\ge48$, $s\ge0$, $p=s+\pi i$, $r=|p|$, $S=\pi/r$, and $c=\min(1/25,4/x)$. Assume $nS^2\ge1$. Write $T$ for the numerator of the original minimum-cycle-length excedance generating function. On a circle of radius $R$, let $F_j$ be the normalized Fourier coefficient of $T(w)/(1+\exp(w-s))$, with frequency factor $\exp(-ij\theta)$.

The theorem selects one radius $R^2=r^2(1+a/k)$ with $a\in\{2-2c,2\}$. Its squared distance in radius from each squared pole modulus is at least $cr^2/k$. With $W=r(r/R)^n/(2|T(p)|)$, both boundary coefficients satisfy

$$
 W|F_n|<\frac1{25},\qquad W\left|\frac rR F_{n+1}-\frac sr F_n\right|<\frac S{25}.
$$

The signed difference keeps the cancellation between the two adjacent rows. The proof combines the selected-circle amplitude, integration by parts, the full odd-pole moments and the uniform decay estimate. [Original-row theorem](FourierOriginalErrorPair.lean)

## Verification

Lean 4.33.1 checked both bounds for the original permutation generating function on the research pin. The bundled checker replayed the final module. The two bounds use the same selected circle. [Verification record and build command](verification.md) · [Independent scope review](review.md)
