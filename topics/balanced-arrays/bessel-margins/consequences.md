# Averaging profile heterogeneity near quota saturation

The [profile lower bound](lower.md) and [profile upper bound](upper.md) give an explicit comparison between scalar and balanced counts after averaging over row deficits. This yields the near-saturation theorem below.

For the original row-capped arrays write $a_k$ for the balanced count and $P(q)=\sum_k a_kq^k$ for its polynomial. Set $D=\lfloor nr/d\rfloor$, $e=nr-dk$ and $h=e/d$. Consider $n/4\le d\le n$ and an internal quota $1\le k<D$, so $h\ge1$. Let
$$
U_e=[z^e]\left(\sum_{j=0}^r\binom d{r-j}z^j\right)^n .
$$

On the scalar conditional profile law take deficits $J_i=r-\ell_i$ with mass proportional to $\prod_i\binom d{r-J_i}$ on $\sum_iJ_i=e$. Given the profile, choose independent uniform row subsets of sizes $\ell_i$. If $Q_k$ is the mean of their equal-column balancing probability over the scalar profile law, then $a_k=U_e Q_k$. In particular the expectation for $Q_k$ is with respect to the scalar conditional profile law, which is fixed before column balance.

## An exact product inequality for conditioned log-concave deficits

Let independent nonnegative integer random variables have positive log-concave mass functions on finite interval supports. Conditioning on their sum, the expectation of a coordinatewise nondecreasing function is nondecreasing in the prescribed sum. Here is a direct discrete proof of the version used below. If the first-coordinate mass is $b_j$ and the mass of the sum of the others is $c_t$, then its conditional mass at total $s$ is proportional to $b_j c_{s-j}$. Convolution preserves interval log-concavity, for instance by multiplying the order-two totally positive Toeplitz matrices and applying Cauchy–Binet. The likelihood ratio between the first-coordinate conditional masses at totals $s+1$ and $s$ is nondecreasing in $j$, since $c_{s+1-j}/c_{s-j}$ is nondecreasing in $j$. On shifting the former coordinate down by one, the ratio to the latter mass is instead nonincreasing since it is proportional to $b_{j+1}/b_j$. The support shifts agree with the two likelihood orders because each endpoint can increase by at most one. Thus the conditional first coordinates can be coupled by their quantiles to differ by either zero or one, with the one at the larger sum. The remaining totals then either coincide or increase by one, so induction couples the full vectors coordinatewise. This is the discrete Efron monotonicity argument. [Efron, 1965](https://doi.org/10.1214/aoms/1177700288)

Now fix the total. Given one coordinate, the expectation of a nonnegative increasing function of the others is nonincreasing in that coordinate, by the preceding monotonicity applied at the residual total. Its covariance with any increasing function of the selected coordinate is therefore nonpositive. Applying this successively to products of coordinate functions, using the constant factor $1$ in omitted coordinates, gives
$$
\mathbb E\!\left[\prod_i f_i(J_i)\,\middle|\,\sum_i J_i=e\right]
\le \prod_i\mathbb E\!\left[f_i(J_i)\,\middle|\,\sum_i J_i=e\right]
$$
for nonnegative nondecreasing $f_i$. This uses no approximation or loss from the probability of the conditioning event.

The conditional marginal of $J_i$ is log-concave because it is proportional to $b_j c_{e-j}$. Its mean is $\bar h=e/n$ by exchangeability. For any log-concave nonnegative integer law of mean $\bar h$, the tails $T_j=\Pr(J\ge j)$ are log-concave. Indeed, $T_{j+1}/T_j$ is a tail-weighted mean of the nonincreasing adjacent mass ratios. Since $T_0=1$, $T_{a+b}\le T_aT_b$. Summing this over positive compositions gives
$$
\mathbb E\binom Jm=\sum_{a_1,\ldots,a_m\ge1}T_{a_1+\cdots+a_m}
\le\bar h^m .
$$
In particular $\mathbb E J^2\le2\bar h^2+\bar h$. For any constant $C\ge0$, the product inequality and the chord bound for $e^{Cx}$ on $[0,1]$ yield
$$
\log\mathbb E\exp\!\left(\frac{C}{d^2}\sum_i J_i^2\right)
\le (e^C-1)\frac{n}{d^2}(2\bar h^2+\bar h).
$$
Thus the deterministic upper overhead $O(h)$ can be replaced after averaging by $O(h^2/n+h/d)$.

For explicit constants, use the same factorial moment bounds coefficientwise in the generating function $\mathbb E(1+w)^J$. It is bounded coefficientwise by $(1-\bar h w)^{-1}$. Differentiating the two series and setting $w=e^t-1$ gives
$$
\mathbb E(J^2e^{tJ})\le
\frac{e^t\bar h}{(1-\bar h w)^2}
+\frac{2e^{2t}\bar h^2}{(1-\bar h w)^3}
$$
whenever $\bar h w<1$. Since $0\le J\le d$, $e^{C J^2/d^2}-1\le(CJ^2/d^2)e^{CJ/d}$. Taking $t=C/d$ and applying the product inequality proves a sharper heterogeneous overhead
$$
\log\mathbb E\exp\!\left(\frac{C}{d^2}\sum_i J_i^2\right)
\le \frac{Cn}{d^2}
\left(\frac{e^t\bar h}{(1-\bar h w)^2}
+\frac{2e^{2t}\bar h^2}{(1-\bar h w)^3}\right).
$$

## Curvature budget

Put $G_k=a_k^2/(a_{k-1}a_{k+1})$. If $G_k\le4$, normalized log-concavity localizes $k$ to $.23n<k<.77n$ for $d\ge n/4$ and $n\ge1024$, by the binomial curvature bound. Thus all three column densities $x_j=j/n$, $j=k-1,k,k+1$, lie in $[.2,.8]$. [Orientation inequality](../orientation-normalization.md) · [Explicit binomial localization](../effective-sectors/sector-proof.md)

Define $L_j=(2\pi n x_j(1-x_j))^{-(d-1)/2}$. The two input bounds give the lower factor $e^{-25(d-1)/(48n)}L_j$ and the averaged upper factor $\sqrt d\,e^{72}L_j$ times the heterogeneous moment with $C=58$. Indeed the original upper prefactor is $\sqrt d(2\pi x_j(1-x_j))^{-1/2}$ and the extra density factor is less than one on $[.2,.8]$. This uses $2\pi x_j(1-x_j)\ge8\pi/25>1$. The upper bound additionally needs $h+1\le n/100$ at the three quotas.

The baseline contributes
$$
2\log L_k-\log L_{k-1}-\log L_{k+1}
=\frac{d-1}{2}\log\big((1-k^{-2})(1-(n-k)^{-2})\big)
\ge -50/n.
$$
Here $-\log(1-z)\le2z$ for $0\le z\le1/2$. Let $M_{-}$ and $M_{+}$ be the logarithms of the profile moments at deficits $d(h+1)$ and $d(h-1)$, respectively. The known scalar deficit curvature then gives
$$
\log G_k\ \ge\
\frac{d(n-1)}{n+d(h+1)-1}\log(1+1/h)
-\log d-144-\frac{25}{24}-\frac{50}{n}-M_--M_+ .
$$
The constant $25/24$ bounds the two lower-factor losses at the center because $d\le n$. The scalar term is at least $(n-1)/((h+1)(h+5))$, by $\log(1+1/h)\ge1/(h+1)$ and $n/d\le4$. [Scalar negative-binomial normalization](../deficit-curvature/scalar.md)

Even without averaging, the deterministic upper $72+9h$ would lose only $18h$ in the curvature. Thus this argument already works at $h=o(n^{1/3})$, or $h\sim c n^{1/3}$ with $18c^3<1$. The moment bound removes this particular restriction.

## Explicit sufficient near-saturation theorem

**Theorem.** If
$$
n\ge \lceil e^{50}\rceil,\qquad n/4\le d\le n,\qquad
1\le k<D,\qquad h\le\tfrac12\sqrt{n/\log n},
$$
then $G_k>4$. At any such center $(-1)^kP(-\sqrt{a_{k-1}/a_{k+1}})>0$ by strict separation and log-concavity. All subsequent internal quotas satisfy the same cutoff, so these signs and the leading sign give at least $D-k$ distinct negative zeros strictly to the left of that node.

To check the constants, write $\ell=\log n\ge50$. Since $\log n\le\sqrt n$ and $n\ge5000^4$, the bound $h+5\le(501/1000)\sqrt{n/\ell}$ holds. In particular $h+1<n/100$. The scalar term is at least $(199/50)\ell$, using $(1-1/n)/(501/1000)^2>199/50$. For either neighbor, $t=58/d\le1/1000$, $w=e^t-1\le(1000/999)t$, and $\bar h_j w\le(1000/999)58(h+1)/n<1/1000$. The two coefficients in the moment bound, after factoring out $\bar h$ and $2\bar h^2$, are bounded by $(1000/999)^5<101/100$. Using the exact relation $\bar h_j=(d/n)(h\pm1)$, the two logarithmic moment losses sum to at most
$$
\frac{101}{100}\,58\left(\frac{4(h^2+1)}n+\frac{2h}d\right)<2.
$$
For the last comparison use $4h^2/n\le1/\ell$ and $4/n+2h/d\le4/n+4/\sqrt{n\ell}<1/1000$. Also $50/n<1/100$. The curvature lower bound becomes
$$
\log G_k\ge\frac{149}{50}\ell-144-\frac{25}{24}-2-\frac1{100}
> \frac32>\log4 .
$$
This contradicts the assumed difficult-node condition and proves the claim without a density assumption on $r/d$. The simple arithmetic facts used here include $\exp(50)>5000^4$, which follows from $e>5/2$ and $(5/2)^{10}>5000$.

## Limiting threshold of this estimate

If $h\asymp\sqrt{n/\log n}$, the scalar term equals $n/h^2+o(1)$, since its expansion error is $O(n/h^3+1/h^2)$. The heterogeneous and Gaussian-baseline losses are $o(1)$. Hence, for a sequence inside the density window, the lower bound is at least
$$
\frac{n}{h^2}-\log d-144-\frac{25(d-1)}{24n}+o(1).
$$
In particular every fixed $c<1$ works asymptotically at $h\le c\sqrt{n/\log n}$. In the critical window $n/h^2-\log d=O(1)$, the remaining additive margin in this formula decides what the bound can certify. A sequence with $\liminf (n/h^2-\log d-25(d-1)/(24n))>144+\log4$ is covered. This budget describes the estimate, rather than a necessary condition on actual roots. The present bounds give no positive guarantee at $h\asymp\sqrt n$ with the current prefactor mismatch.

A natural next condition is a lower factor $\sqrt d\,L_j e^{-C_-}$ matching the upper up to a constant exponential, or a direct comparison that cancels the prefactor in the curvature. With matched prefactors, at $h\sim c\sqrt n$ the same calculation gives the finite lower budget $c^{-2}-144-2C_--232c^2+o(1)$. Dense fixed-margin asymptotics already exhibit the natural factor $\sqrt d\,L_j$: Stirling’s formula in $\binom nk^d/\binom{nd}{dk}$ gives that factor up to a bounded exponential in the current aspect and density intervals. Canfield–Greenhill–McKay’s theorem controls regular profiles asymptotically with its own margin assumptions. The present inputs instead supply explicit inequalities, the upper on every profile, and profit from averaging the exact scalar law. Near-saturation switching bounds based on retaining a fixed full-row bulk similarly yield explicit estimates, but their hypothesis requires the number of potentially defective rows to fit that common bulk. [Canfield–Greenhill–McKay, Theorem 1](https://doi.org/10.1016/j.jcta.2007.03.009) · [Local quantitative profile comparison](../dense-regime/quantitative-margins.md) · [Common-bulk switching bound](../effective-upper-curvature/proof.md)

## Necessary band for a failure of real-rootedness

Take $n\ge\lceil e^{50}\rceil$ and $.295n\le d<n$. Write $\Pi_i=G_i/g_i=p_i^2/(p_{i-1}p_{i+1})$, where
$$
g_i=\big((1+1/i)(1+1/(n-i))\big)^d,\qquad p_i=a_i/\binom ni^d .
$$
If the original polynomial has a nonreal zero, then some internal index $k$ satisfies all three conditions
$$
G_k\le4,\qquad \Pi_{k-1}>\Pi_k,\qquad
\frac12\sqrt{\frac n{\log n}}<\frac{nr}{d}-k<
1+n\sqrt{\frac{8\log n}{d}}.
$$
The difficult-node localization ensures $k-1$ is an internal index. The assertion only gives a necessary condition.

The existing rare-overflow result supplies $G_k\le4$, the drop in $\Pi_k$, and the upper deficit bound. The cap is proper in any such failure, since the full-cap family is real-rooted. The explicit near-saturation theorem above excludes a difficult node at or below the lower deficit bound. [Rare-overflow strip](../engset-curvature/rare-overflow-strip.md) · [Tilted sign criterion](../engset-curvature/curvature-reduction.md)

## Exact finite outer-root examples

The [rational witness generator](certificates.py) and its [exact output](certificates.jsonl) apply the same budget directly, without the coarse asymptotic row cutoff. Specifically, it replaces $\log(1+d/e)$ by $2d/(2e+d)$, and upper-bounds $\log d$ by $(7/10)\lceil\log_2d\rceil$. It uses the minimum of the deterministic $9e/d$ and the averaged penalty with $e^{58/d}\le d/(d-58)$ where its denominator is positive. All subsequent calculations use exact fractions.

The generator certifies a terminal block of internal indices with $\log G_k>11/5>\log9$. Let $k_0$ be its first index. At $|q|=x_{k_0}=\sqrt{a_{k_0-1}/a_{k_0+1}}$, log-concavity bounds the relative sum of all other term magnitudes by $2/(\sqrt{G_{k_0}}-1)<1$. Rouché's theorem gives exactly $k_0$ zeros inside and no zeros on that circle. The terminal alternating signs give $D-k_0$ distinct negative zeros outside. Thus they account for every zero outside that circle, and each is simple. The exact examples at $d=3n/10,\ r=d/2$ yield $2,5,22,76,244$ such roots, respectively, for $n=4000,10000,100000,1000000,10000000$. These bounds do not claim anything about zeros inside the corresponding radius.
