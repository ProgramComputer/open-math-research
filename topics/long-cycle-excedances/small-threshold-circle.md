# All thresholds below 400 from size one million

For every $n\ge10^6$ and $3\le k<400$, the nonzero roots of the minimum-cycle-length excedance rows at $n$ and $n+1$ are simple, negative and strictly interlace. This covers the small thresholds omitted by the [wider-circle theorem](radial-taylor.md).

For $k\le10$ the [previous short-cycle criterion](effective-uniform.md) applies. At $n=10^6$, $n/2000=500>30\log n+20$ and the difference increases thereafter. Assume $11\le k<400$. Keep the notation of the wider-circle proof. The logarithm $G$ of its numerator $T_s$ is a polynomial of degree at most $k-1$. The earlier short-cycle proof gives $|G(w)|\le 6+10\log k$ on the circle of radius $r(1+1/(50k))$. For any polynomial $p$ of degree at most $d$ and $R\ge R_0>0$, the maximum on radius $R$ is at most $(R/R_0)^d$ times the maximum on radius $R_0$. Apply the maximum principle to $z^d p(1/z)$ on the reciprocal disk.

On $|w|\le r(1+1/(5k))$ we therefore have $|G(w)|\le e^{1/5}(6+10\log k)<82$. The ratio $|T_s(w)/T_s(w_1)|$ is below $e^{164}$. Choose a radius between $r(1+3/(20k))$ and $r(1+1/(5k))$ at distance at least $\delta=\min(r/(80k),1/r)$ from every pole. The interval has length at least $4\delta$ and adjacent pole radii near it differ by more than $2\delta$, by the same subtraction of squares as in the wider-circle proof. The inverse denominator on it is bounded by $4/\delta$. For $nS^2\ge1$ both normalized circle errors are bounded by

$$
2(80k+r^2)\exp(164-0.148n/k)<S/100.
$$

Indeed $k\log(1+0.15/k)>0.148$ and $80k+r^2<90n$. At $n=10^6$, $0.148n/400>164+10+(3/2)\log n$, and the difference increases thereafter. Use $e^{10}>18000$ and $S\ge n^{-1/2}$.

If $s\le9\sqrt k$, the increase of squared radius is at most $(81k+\pi^2)(2/(5k)+1/(25k^2))<34<8\pi^2$. Only the principal pair is enclosed. If $s>9\sqrt k$, the enclosed pole segments satisfy $\log(|w|/s)\le(1/5+\pi^2/162)/k<0.262/k$. For $k\ge21$ the [gamma density derivative estimate](effective-uniform.md) gives

$$
\pi|H'(w)|\le\pi e^{0.262}\left(\frac1{9\sqrt{21}}+\frac1{\sqrt{40\pi}}\right)<12/25 .
$$

For $11\le k\le20$ one has $s>9\sqrt k>2(k-1)$ and $s>29$. Each normalized gamma-density summand is then at most the Poisson lower-tail probability $e^{-as/8}$, so $\pi |H'|\le\pi e^{0.262}/(e^{29/8}-1)<12/25$ as well. On the chosen radius each enclosed pole satisfies $(p^2-1)S^2\le(1+1/(5k))^2-1<0.038$. With $u=(p^2-1)S^2\le0.038$, one has $\log(1+u)\ge u-u^2/2\ge0.981u$. Hence $|z_p|^n\le e^{-0.49(p^2-1)}$ when $nS^2\ge1$. These are exactly the hypotheses yielding weighted nonprincipal error below $21/50$. The outer endpoint $s_{\ast}>2\sqrt n>9\sqrt k$ gives the required phase bound there. The [common-residue sign comparison, reflection and root count](radial-taylor.md) apply. This argument concerns both actual consecutive rows. Formal verification is ⬜ None.

Run `python3 -B verify_small_threshold_circle.py` from this directory to replay the [exact rational checks](verify_small_threshold_circle.py).
