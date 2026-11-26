# Joining the half-square-root exterior proof to the middle

For every $n\ge1{,}000{,}000$ and $3\le k\le n$, the true nonzero roots of the long-cycle excedance rows at $n$ and $n+1$ are simple and negative, and strictly interlace. The improvement uses the [half-square-root exterior analysis](README.md) for $20\le n/k\le100$. The wider circle deals with larger aspects. This is an explicit sufficient region for Alexandersson's all-size conjecture.

## Pole estimates at the stronger join

Write $x=n/k\in[\ell,X]$. At the new first sample, $nS^2>49/20$ and $A>\sqrt{(49/20)n}/x$. The existing [degree-split proof][degree] uses the angle bound only for the single-pole errors and the two positive pole envelopes. The former bounds improve automatically, so retain $1/50$ and $1/16$. The proof can take

$$
w_p=\left(1+\frac{48951}{3840000X}(p^2-1)\right)^{-96},
\qquad
v_p=\left(1+\frac{49(\ell-1)}{7680\ell}(p^2-1)\right)^{-96}
$$

instead of its original envelopes. The first follows from $(k-1)S^2\ge(999/1000)(49/(20X))$ and Bernoulli at exponent $(k-1)/192$. The second follows from $MS^2\ge(1-1/\ell)(49/20)$ for the two outputs $M=n,n+1-k$, and Bernoulli at exponent $M/384$. The partial fractions, numerator moments, degree split and derivative sums are otherwise identical. These are strictly positive bounds for the same inequalities proved there, including both insertion signs in the middle region.

For a checked minimum $A_0$, the join needs $n\ge\lceil20(XA_0)^2/49\rceil$, together with the exterior and envelope base conditions. The exact comparisons give the following table.

| Aspect interval | Minimum $A$ | Sufficient old size |
| --- | ---: | ---: |
| $20\le x\le25$ | 24 | 1,000,000 |
| $25\le x\le32$ | 21 | 1,000,000 |
| $32\le x\le40$ | 18 | 1,000,000 |
| $40\le x\le50$ | 17 | 1,000,000 |
| $50\le x\le64$ | 16 | 1,000,000 |
| $64\le x\le80$ | 16 | 1,000,000 |
| $80\le x\le92$ | 16 | 1,000,000 |
| $92\le x\le96$ | 16 | 1,000,000 |
| $96\le x\le100$ | 17 | 1,179,592 |

The old integer samples from $H+1$ to $n-H-1$ give $n-2H-2$ middle zeros, and the two groups of $H$ exterior zeros then exhaust the old degree. Thus the sign at each old zero is fixed by its rank in the corresponding middle gap or exterior group. The actual next signs alternate throughout, and the next constant and leading coefficients are positive, giving both outside zeros and one new zero between every adjacent old pair. Degree exhaustion gives strict interlacing and simplicity.

## Uniformity at one million

For $n\ge4{,}062{,}720$, use the [earlier uniform result][adaptive]. For $10^6\le n<4{,}062{,}720$, proceed as follows.

- Thresholds $k<400$ are covered by the [smaller-threshold circle][small].
- The [complete three-cycle theorem][three] covers $x<4$. The earlier [bounded-aspect table][degree] covers $4\le x\le20$ throughout these rows.
- The enhanced exterior and middle proof above covers $20\le x\le96$.
- For $x\ge96$ and $k\ge400$, the [wider-circle criterion][radial] applies because $0.89\cdot96>47+2.5(15.3)>47+2.5\log n$.

The theorem concerns the actual next row. The middle estimate here additionally gives the sign of the opposite insertion pencil, while the new exterior comparison only needs the actual next row. Neither conclusion resolves the lower finite range.

Run `python3 -I -B check-middle.py` to reproduce the rational pole-envelope means, the table and the uniform overlap. Its lattice and geometric summations are the same as in the earlier exact checker, with the larger angular input substituted. [Exact replay](middle-output.txt) · [Independent review](review.md)

[adaptive]: ../adaptive-poles/README.md
[degree]: ../adaptive-poles/degree-split.md
[small]: ../small-threshold-circle.md
[three]: ../three-cycle-complete.md
[radial]: ../radial-taylor.md
