# Adaptive exterior centers and weighted old-row tails

Write $P=E_{n,k}$, $c_j=[X^j]P$, and $\alpha_j=c_j/j^n$ for $j>0$. Use $n\ge10^4$, $k\ge2$, and $n>4000k$ for the checked old-row lower bound. Put $y=\sqrt n$, $H=\lfloor7y/20\rfloor$, and $J=\lfloor y/2\rfloor$. Fix a central rank $1\le h\le H$. All central indices needed for an adjacent-center comparison lie through $J$ since $H+2\le J$. For each $1\le j\le J$ the checked coefficient bounds give

$$
\alpha_j\left(1+\tfrac83 kj/n\right)\ge\tfrac{99}{100},
\qquad 0<\alpha_j\le1,\qquad (kj/n)\alpha_j\le\tfrac{151}{100}.
$$

The global original coefficient envelope gives $0\le\alpha_j\le1$ at every $j>0$. The constant coefficient of $P$ vanishes. Indeed an admissible permutation has a nontrivial cycle and every such cycle has a strict excedance.

For $1\le i,j\le J$, multiply the lower estimate at $i$ by $\alpha_j$ and use both upper estimates at $j$. This gives the near-index ratio

$$
\frac{\alpha_j}{\alpha_i}\le
\frac{100}{99}\left(1+\frac83\frac{151}{100}\frac{i}{j}\right)
\le \frac{51}{10}\max(1,i/j).
$$

Consequently $\rho_h=\alpha_h/\alpha_{h+1}$ is positive, and both $\rho_h$ and $\rho_h^{-1}$ are at most $51/5$. For $h\ge6$ the bound on $\rho_h$ improves to $(51/10)(7/6)<6$, while its reciprocal is already at most $51/10$.

Use the actual center $u_h=c_h/c_{h+1}=\rho_h(h/(h+1))^n$. Define $q_h=(1-1/(h+1)^2)^n$. Because $H+1\le(9/25)y$, one has $q_h\le e^{-625/81}<1/2200$. For $h\le5$, the exponent bound improves to $n/(h+1)^2\ge 10^4/36>9$, so $q_h<1/4000$. The exponential inequalities may be checked with rational arithmetic. For the first, use $e>2718/1000$ and the first four Taylor terms at $58/81$ to bound $e^{625/81}=e^7 e^{58/81}$. For the second, $(27/10)^9>4000$ suffices. Thus in both rank ranges

$$
\frac{8q_h}{7\rho_h}<\frac1{300},
\qquad
\frac98 \rho_h q_h<\frac1{300}.
$$

The right inequality for $h\ge6$ still has room after substituting $6$ for $\rho_h$, while $h\le5$ uses $51/5$ and $1/4000$. The left inequality uses the corresponding bound on $\rho_h^{-1}$.

At the left endpoint $L=7u_h/8$, write $j=h-\ell$ with $1\le j<h$. Direct normalization by $c_h$ gives

$$
\frac{c_j/L^\ell}{c_h}
=\frac{\alpha_j}{\alpha_h}\left(\frac{8}{7\rho_h}\right)^\ell
\left[\frac{j}{h}\left(\frac{h+1}{h}\right)^\ell\right]^n.
$$

Bernoulli's inequality gives $j/h=1-\ell/h\le(1-1/h)^\ell$. The quantity in brackets is at most $(1-1/h^2)^\ell\le(1-1/(h+1)^2)^\ell$. Because $h/j\le\ell+1$, the weighted coefficient is at most $(51/10)c_h(\ell+1)(1/300)^\ell$. The omitted $j=0$ case has coefficient zero, including when $h=1$.

At the right endpoint $U=9u_h/8$, write $j=h+1+\ell$ with $\ell\ge1$. The central coefficient at $h+1$ has weight exactly $(9/8)c_h$. Therefore

$$
\frac{c_j U^{j-h}}{c_h}
=\frac98\frac{\alpha_j}{\alpha_{h+1}}\left(\frac98\rho_h\right)^\ell
\left[\frac{j}{h+1}\left(\frac{h}{h+1}\right)^\ell\right]^n.
$$

By Bernoulli the bracket is at most $(1+1/(h+1))^\ell(h/(h+1))^\ell=(1-1/(h+1)^2)^\ell$. For $j\le J$ the coefficient ratio is at most $51/10$. For $j>J$, one has $j>y/2$, hence $\ell>(7/50)y\ge14$ and $h+1<(18/7)\ell$. Using $k\le n$ and the lower bound at $h+1$ gives

$$
1/\alpha_{h+1}\le(100/99)(1+(8/3)(h+1))<8(\ell+1).
$$

Together with the global bound $\alpha_j\le1$, this gives the same desired expression on both ranges, namely $c_jU^{j-h}\le9c_h(\ell+1)(1/300)^\ell$.

For the upper center cap, $\rho_h\le51/5$ and monotonicity of $h/(h+1)$ give $u_h\le(51/5)(H/(H+1))^n$. The exact neighboring identity is

$$
\rho_hq_h u_{h+1}=\rho_{h+1}u_h.
$$

The established bound $q_h\le1/2200$ and $1\le(51/5)\rho_{h+1}$ satisfy the adjacent-center theorem in #275. It gives $20u_h<u_{h+1}$ and hence the ordering of the positive boxes imposed by #277.

## Far insertion lag

For $j>J$, the same right-side argument also bounds $(j^n)U^{j-h}$ by $9c_h(\ell+1)(1/300)^\ell$. This uses $1/\alpha_{h+1}$ directly and sets the numerator of the normalized coefficient ratio to 1. Since $j=h+1+\ell<4\ell$, any nonnegative lag coefficient bounded by $j^{n+1}$ meets the far criterion in #277. The checked original_color_successor_lag bounds the lag by the increment of the transformed coefficients. Both transformed coefficients are nonnegative, and the upper row's coefficient is at most $j^{n+1}$ by original_color_count_eq_transform and realCount_bounds. This supplies the trivial lag bound with the factor of $X$ already included in originalFrontLag.

The near insertion bound $V_j\le(8/25)c_j$ remains separate from the coefficient envelopes of the old row. The small common growth ratio above uses $h\le H$, while the near coefficient comparison itself is valid through $J$.

[Exact #277 interface](https://github.com/ProgramComputer/open-math-research/blob/e5fac89b16dc83f80a2128c9b4a38010cec2516c/topics/long-cycle-excedances/lean/front-envelope-sums/RepositoryExteriorEnvelopes.lean)
