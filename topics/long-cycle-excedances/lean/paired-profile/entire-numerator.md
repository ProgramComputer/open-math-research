# Evaluating the original cycle numerator at every pole

Let $d_s$ be the proportion of permutations of $s$ labels whose cycles have length at least $k$. Set $p_0=0$ and $p_s=d_s$ for $s>0$. The literal numerator coefficients are $b_0=0$ and $b_s=p_s-p_{s-1}$ for $s\ge1$. For $k\ge2$ and every $v\in\mathbb C$ the series converges absolutely and

$$
\sum_{s\ge0}b_s v^s=\exp\left(-\sum_{r=1}^{k-1}\frac{v^r}{r}\right)-(1-v).
$$

The proof starts with cutoff one, for which $d_s=1$. Increasing the cutoff from $r$ to $r+1$ multiplies the denominator-cleared series by the entire function $\exp(-v^r/r)$. Its formal exponential is supported on multiples of $r$. Reindexing its ordinary exponential series proves absolute convergence at every point. The Cauchy product then proves the assertion by induction on the cutoff. The constant and linear corrections come from deleting the empty permutation before the denominator is cleared. [Formal evaluation](EntireCycleEvaluation.lean) · [Literal probability coefficients](RepositoryNumeratorVariation.lean)

For the signed pole denominators $w_q=C+i(2q+1)S$, take $S\ne0$ and distinct indices $a,q$. Evaluating the actual occupied primitive at $w_a$ uses the series above at $v=w_a/w_q$. For $|v|\le1$ the complete factor equals $\exp L_k(v)$ with $L_k$ the radial logarithm. This includes the two conjugate principal poles. The same equality holds for a finite product of the factors, with the corresponding logarithms added. [Original enumerator and product theorems](RepositoryPrincipalFactor.lean) · [Radial identity](../sine-comparison/PrincipalFactor.lean)

At the distinguished pole $a=0$, the logarithms of all the other evaluated factors are absolutely summable. The product over the whole signed lattice is the exponential of their sum. The proof uses the spacing between distinct poles and absolute convergence of the inverse-denominator powers. At unit principal radius it reduces a lower bound on the real part of the actual product to an upper bound on one sum of positive real terms. [Infinite product and scalar reduction](PrincipalLatticeProduct.lean)

The generic series and the finite and infinite occupied-factor theorems passed local Lean 4.19. The local literal probability adapter took the established permutation recurrence as an explicit hypothesis. The production source imports the proven recurrence. Lean 4.33.1 compiled and replayed all 38 inputs, and all 74 named axiom reports used only standard axioms. [Verification record](principal-verification.md) The numerical comparison across the nine aspect ranges remains open in Lean.

An independent exact computation enumerates every permutation of sizes one through nine and compares all 90 numerator coefficients for cutoffs two through ten with finite products of signed exponential series. [Checker](check-entire-numerator.py) · [All coefficients](entire-numerator-output.txt)

From the repository root run

~~~sh
python3 -I topics/long-cycle-excedances/lean/paired-profile/check-entire-numerator.py
python3 -I topics/long-cycle-excedances/lean/paired-profile/check.py /tmp/paired-numerator
~~~
