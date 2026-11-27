# Bounding the principal convolution by 241 bin coefficients

For the adjacent long-cycle excedance determinant, the principal pole contributes a centered convolution error. Fix $n\ge10000$, a cutoff $k\ge2$, an integer lower aspect bound $\ell$ with $\ell k\le n\le48k$, and $S=\sin\theta>0$ with $nS^2\ge6/5$. The estimate holds for each finite pole set at every truncation degree. The theorem takes the linear bin bounds and the integer recurrence for the product coefficients as inputs. [Exact statement](PrincipalBinHeadTail.lean) · [Original adjacent determinant](../../sine-comparison/README.md)

Write $w_q=\cos\theta+i(2q+1)S$ and let $Q$ be the finite product of occupied factors over the poles other than $q=0$. Write $c_k=\exp(-H_{k-1})$ and let $p_r$ be the cutoff probability with weight zero below $k$. Define the error

$$
U_n=\sum_{t=0}^n p_{n-t} [u^t]Q(u) w_0^t-c_k Q(w_0).
$$

Let $q_b/G$ be the rounded upper bound for bin $b$ furnished by the integer recurrence. Set $j_b=\min(40,\max(0,\ell-\lceil b/4\rceil))$ and let $e_j$ be the [checked centered probability bound](ProbabilityErrorBands.lean). Then

$$
2k|U_n|<2\sum_{b=0}^{240}e_{j_b}\frac{q_b}{G}+\frac1{10000}.
$$

**Why the two indices matter.** The bin of a product is the sum of the individual bins $\lceil4s/k\rceil$. At $k=5$, two factors of degree eight have total degree 16 and bin 14. A single factor of degree 16 has bin 13. The proof marks each factor before multiplying, then uses $4t\le kb\le5t$ on the support of the resulting polynomial in degree $t$ and bin $b$. Thus $j_b k\le n-t$ whenever $t\le n$, and $j_b=0$ for supported terms with $t>n$. Summing over degrees at fixed bin uses its budget once. Absolute convergence then removes the degree truncation. [Coefficient comparison](MarkedCoefficientComparison.lean) · [Weighted sums](WeightedMarkedBins.lean) · [Probability bound on supported bins](CenteredBinGeometry.lean) · [Limit of the convolution](CenteredMarkedProduct.lean)

**The tail.** At $B=9/8$, the isolated numerator jump and the factorial block bounds give $k\sum_{s=k}^N |p_s-p_{s-1}|B^{\lceil4s/k\rceil}<16$ for every $N$. In block $hk<s\le(h+1)k$ the tilted contribution is at most $2^{h+1}/h!$. Summing gives $2e^2<16$. Independently of $N$, the reflected positive kernel of the distinguished pole satisfies

$$
\sum_{q\in T}\frac{|w_q^{-1}|^{k-1}}{2|q|kS}\le\frac45
$$

for every finite set $T$ omitting zero. Consequently the sum of tilted absolute primitive masses is at most $64/5$. The product of one plus these masses is bounded by $e^{14}$. The part beyond bin 240 of the two principal terms is bounded by $2(4/7)B^{-240} e^{14}<1/10000$. [Numerator estimate](TiltedNumeratorMass.lean) · [Finite positive kernel](PrincipalRowKernel.lean) · [Absolute product estimate](LiteralPrincipalTilt.lean) · [Tail arithmetic](BinCostTail.lean)

Local Lean 4.19 checked the analytic reduction with the standard axiom set. The Lean 4.33.1 port is in replay. Evaluating the nine finite head sums supplies numerical bounds for this error. The nonprincipal value, regular numerator, and cutoff-atom errors are the remaining three terms of the determinant proof. [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)
