# The principal denominator on the comparison circle

Put $z=(s+i\pi)/k$ and $q=r/k$, where $s\ge0$, $r=\sqrt{s^2+\pi^2}$ and $k\ge100$. For every height,

$$
|1-e^{-z}|\ge \frac{q}{2+q}.
$$

If $q\le\pi$, the modulus is at least $q/5$. If $q\le12\pi/25$, it is at least $q/3$. These are the three principal denominator estimates used in the large-aspect interlacing proof. [Original quantitative comparison](../../fourier-circle/README.md) · [Formal statement](FourierExponentialGap.lean)

For $u=\Re z\ge0$ and $0\le v=\Im z\le\pi/2$, integrate $e^{-tz}$ over $0\le t\le1$. Its real part is at least $e^{-tu}\cos v$. The integral of $e^{-tu}$ is at least $1/(1+u)$ by $e^u\ge1+u$. Multiplying by $|z|$ gives the bound $|1-e^{-z}|\ge |z|\cos(v)/(1+u)$. Here $v\le1/10$, so $\cos v\ge99/100$. This proves the two bounded-height estimates and the first estimate for $q\le1$. For $q>1$, use $q\le u+v\le u+1/10$ and $|1-e^{-z}|\ge1-e^{-u}\ge u/(1+u)$.

## Verification

The three named statements passed Lean 4.19.0 at `6caaee842e94` and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All three transitive axiom reports listed `propext`, `Classical.choice` and `Quot.sound`. The hosted check is pending. The numerator contraction and the denominator throughout the integration circle enter separately in the comparison.

~~~sh
cd shared/lean
lake env python3 -I ../../topics/long-cycle-excedances/lean/fourier-circle/check.py
~~~
