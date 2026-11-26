# An effective central interval for arbitrary cycle counts

Assume $n\ge k\ge3$. For $t=-e^{-s}$, $s\ge0$, set $\theta=\arg(s+i\pi)$ and $S=\sin\theta$, with $F_n$ and $z_p$ normalized as in the [two-cycle proof](https://github.com/ProgramComputer/open-math-research/blob/main/topics/long-cycle-excedances/two-cycle-band.md). At $kS^2\ge8$, the following argument gives the sign of $F_n$ at every sample $\theta=l\pi/n$ and the strict estimate $|L|<|t(1-t)P_n'|$ at every real root in the interval. This interval uses no restriction on the number of cycles. In terms of root modulus, reciprocity extends the estimate to $|\log|t||\le\pi\sqrt{k/8-1}$ for $k\ge8$.

Write $D(u)=\sum_m d_m u^m$ for the ordinary cycle-probability series. Let $f_m$ be the coefficient from the two principal factors $D(z_1u)D(z_{-1}u)$ and $h_m$ from the product of all the other factors. Then $F_n=\sum_{j=0}^n h_jf_{n-j}$. In particular $h_0=f_0=1$, and each coefficient with index in $(0,k)$ vanishes identically. The variation estimate gives
$$
|f_m-2d_m\cos(m\theta)|\le 2/(k^2 S),\qquad
|f_m'/m+2d_m\sin(m\theta)|\le3/(k^2 S)\quad(m\ge k).
$$
In particular $|f_m|,|f_m'|/m<3/k$. [Discrete variation estimate](cycle-probability-variation.md)

Let $\rho_p=|z_p|$. Since $k\ge8$ and $kS^2\ge8$, monotonicity of $(1+b/k)^k$ gives $\rho_p^k\le |p|^{-8}$. Therefore
$$
\varepsilon=\sum_{|p|\ge3,\,p\ {
m odd}}|p|\rho_p^k\le2\sum_{m\ge3}m^{-7}<2\int_2^\infty x^{-7}\,dx=1/192 .
$$
For $x=(p^2-1)S^2$ we have $(1-\rho_p)^{-1}=1+(1+\sqrt{1+x})/x\le2+2/x$. It follows that $1/(k(1-\rho_p))<1$ for these nonprincipal poles. The nonconstant coefficients of $D(z_pu)$ have total absolute mass at most $a_p=\rho_p^k/[k(1-\rho_p)]\le\rho_p^k$. Their largest absolute coefficient is at most $\rho_p^k/k$. The product of all $(1+a_p)$ is less than $e^\varepsilon<2$.

For a monomial in the factors with positive total index $j$, its derivative divided by $j$ has absolute value at most its absolute coefficient times the sum of $|p|$ over occupied poles. Indeed $|z_p'/z_p|\le |p|\rho_p\le |p|$, and each part's share of the total degree is at most one. Sum over a distinguished occupied pole. Bounding its positive coefficient mass by $a_p$ and all other factors by their absolute sums gives
$$
\sum_{j\ge1}|h_j|\le2\varepsilon,\qquad
\sum_{j\ge1}|h_j'|/j\le2\varepsilon .
$$
For each fixed output index $j$, the same convolution bound uses the supremum $\rho_p^k/k$ on the distinguished factor and the absolute sums on all other factors. This gives $|h_j|,|h'_j|/j\le2\varepsilon/k$ for $j\ge1$. The bounds follow first for a finite collection of poles, and pass to the coefficientwise infinite product by absolute convergence. Termwise derivatives at any positive angle are justified locally by comparison to the summable powers $|p|^{1-k}$, with a constant allowed to depend on the angle and the fixed degree.

Separate $j=n$ from the convolution terms with $1\le j<n$. The two bounds on $h$, and the $3/k$ estimates for $f$ and its normalized derivative, show
$$
|F_n-f_n|\le8\varepsilon/k,\qquad
|F_n'-f_n'|/n\le14\varepsilon/k .
$$
In the derivative comparison both degree fractions $j/n,(n-j)/n$ are at most one. Since $2d_n\ge2/(2k-1)>1/k$ and $kS\ge kS^2\ge8$, the comparison with the principal cosine gives the claimed sample sign and $|\cos(n\theta)|<3/10$ at an old zero. There $|\sin(n\theta)|>19/20$, while $3/(kS)+14\varepsilon<9/20$. Consequently $|F_n'|>n/(2k)$. In particular these old roots are simple.

At an old zero the derivative and lag, after multiplication by the same factor, are $S F_n'$ and $B_k F_{n+1-k}$, with $B_k=\sum_p z_p^k$. This normalization follows from the insertion recurrence for every cycle count. If the residual index is below $k$, the lag vanishes. Otherwise $n\ge2k-1$, so $nS\ge2kS-S\ge15$. Since $|B_k|\le2+\varepsilon$ and $|F_{n+1-k}|\le(2+2/8+8\varepsilon)/k$, the lag has magnitude below $5/k$, strictly smaller than $S |F'_n|>15/(2k)$.

For $k\ge8$ let $J=\lceil(n/\pi)\arcsin\sqrt{8/k}\rceil$. Reciprocity gives $F_n(\pi-\theta)=(-1)^n F_n(\theta)$ and scales the two insertion terms at reciprocal roots by the same factor. The samples with indices $J,\ldots,n-J$ therefore alternate in sign. In each complete gap between them $\sin(n\theta)$ has a fixed sign. At every zero there the derivative comparison proved above gives $`\mathrm{sgn}\,F_n'=-\mathrm{sgn}\,\sin(n\theta)`$. All the zeros in that gap would consequently be simple crossings of the same orientation. Two consecutive simple zeros must cross in opposite directions, so every such gap contains precisely one zero.

In particular $P_n$ has at least
$$
\max\left(0,n-2\left\lceil\frac n\pi\arcsin\sqrt{8/k}\right\rceil\right)
$$
distinct simple negative roots in the stated region. Between two consecutive old roots obtained in this way, $P_{n+1}$ has a zero, by the insertion signs. For $k=8$ the interval consists of the point $-1$ and there are no complete gaps.

This gives an explicit central part of the induction for every row at every threshold $k\ge8$. The remaining angles satisfy $k\sin^2\theta<8$. In particular the result need not reach the intervening roots between this interval and the smallest roots handled by a coefficient estimate. **⬜ None.** This is a written partial theorem. [Independent agent-assisted review](review-central-interval.md) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)
