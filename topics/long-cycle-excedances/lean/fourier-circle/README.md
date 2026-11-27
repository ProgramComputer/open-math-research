# Fourier identities for the consecutive-row comparison

The large-aspect proof estimates two consecutive coefficients on the same circle. The subtraction has to occur before absolute values are taken. Lean checks the signed identity for periodic functions satisfying the kernel equations and evaluates the squared norm of each individual pole. These are supporting lemmas for the [common-circle proof](../../fourier-circle/README.md).

## Signed coefficient identity

Write $`\widehat f_j=(2\pi)^{-1}\int_0^{2\pi} f(x)e^{-ijx}\,dx`$ and $m=n-k$. Suppose $f$ and $B$ have matching endpoint values, $D$ and $E$ are continuous, and

$$
f'=i e^{ikx}fD,\qquad B'=iE,\qquad (ae^{-ix}-C)D=B+Ae^{-ix}.
$$

For integer $n,k$ and complex constants $a,C,A$, the checked identity is

$$
mn(a\widehat f_{n+1}-C\widehat f_n)
=\widehat{f(e^{ikx}DB+E)}_m
 +mA\widehat f_{n+1-k}-ma\widehat f_{n+1}.
$$

The first integration by parts shifts the frequency by $k$. The pole split contributes the frequency $n+1-k$. A second integration gives the product $mn$ without dividing at frequency zero. The modules also contain the unweighted identity for the old row. [Periodic integration](FourierCircleShift.lean) · [Product and old-row identities](FourierCircleContrast.lean) · [Adjacent-row identity](FourierAdjacentIdentity.lean)

## Squared norm of a pole

For any complex $p$ and real radius $R>0$ with $|p|\ne R$, Lean proves

$$
\int_0^{2\pi}\frac{dx}{|p-Re^{ix}|^2}
=\frac{2\pi}{\bigl||p|^2-R^2\bigr|}.
$$

For $p\ne0$, reflection through the circle pairs $p$ with $R^2/\overline p$. Exactly one lies inside. Partial fractions reduce the integral to the difference of their Cauchy integrals. At $p=0$ the integrand is constant. [Pole integral](FourierPoleMoment.lean)

## Weighted pole products

Set $u_p(x)=\sqrt{\bigl||p|^2-R^2\bigr|}/|p-Re^{ix}|$. Each $u_p$ has squared integral $2\pi$. Integrating $(u_p-u_q)^2\ge0$ bounds the integral of $u_pu_q$ by $2\pi$, including poles on opposite sides of the circle. For two finite pole lists and arbitrary nonnegative weights, it follows that

$$
\int_0^{2\pi}\Big(\sum_i a_i u_{p_i}(x)\Big)\Big(\sum_j b_j u_{q_j}(x)\Big)\mathop{}\mathrm{d}x
\le 2\pi\Big(\sum_i a_i\Big)\Big(\sum_j b_j\Big).
$$

The two lists may overlap or include repeated locations. [Two-pole bound](FourierPolePair.lean) · [Weighted finite products](FourierFinitePoleBound.lean)

The same bound holds for two countably infinite lists with summable nonnegative weights. On each list only finitely many poles may have modulus below $2R$, and each pole must avoid the circle. For $|p|\ge2R$ the normalized kernel is at most $2$, uniformly in angle. The finitely many near poles also have a common bound, since each misses the circle. This gives an integrable constant majorant for the product of partial sums and justifies passage to the limit. [Uniform bound](FourierPoleUniform.lean) · [Infinite weighted products](FourierInfinitePoleBound.lean)

For the complex sums themselves, put $K_p=1/\sqrt{\bigl||p|^2-R^2\bigr|}$. With the same hypotheses on the poles and finite weighted sums on the right, Lean proves

$$
\int_0^{2\pi}
\left|\left(\sum_i\frac{c_i}{p_i-Re^{ix}}\right)
       \left(\sum_j\frac{d_j}{q_j-Re^{ix}}\right)\right|\mathop{}\mathrm{d}x
\le 2\pi\left(\sum_i|c_i|K_{p_i}\right)\left(\sum_j|d_j|K_{q_j}\right).
$$

Both complex series converge absolutely at every angle and define continuous functions. This covers the product of the unweighted and contrast-weighted kernels once their pole weights are shown to be summable. [Complex pole products](FourierComplexPoleBound.lean)

## Verification

The research pin is Lean 4.19.0 at `6caaee842e94` and mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The nine common-circle modules compiled locally. Their eighteen named axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`. The checker compiles in a fresh directory and verifies the named reports. [Source checker](check.py) · [Dependency manifest](../../../../shared/lean/lake-manifest.json) · [Hosted check](../../../../.github/workflows/long-cycle-fourier-contrast.yml)

```sh
cd shared/lean
lake exe cache get Mathlib.Analysis.Complex.CauchyIntegral Mathlib.Analysis.Complex.RealDeriv Mathlib.Analysis.SpecialFunctions.ExpDeriv Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus Mathlib.Tactic.FieldSimp Mathlib.Tactic.LinearCombination Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Tactic.Positivity Mathlib.MeasureTheory.Integral.DominatedConvergence Mathlib.Analysis.NormedSpace.FunctionSeries Mathlib.Analysis.PSeries Mathlib.Data.Real.Pi.Bounds Mathlib.Tactic.Linarith Mathlib.Analysis.Calculus.SmoothSeries
lake env python3 -I ../../topics/long-cycle-excedances/lean/fourier-circle/check.py
```

The hosted Linux check at `63c4e95` passed all eighteen named theorem audits. Each of the nine source digests in its log matches the corresponding Git blob. [Hosted verification record](https://github.com/ProgramComputer/open-math-research/actions/runs/46000239509)

The verification still requires the differential equations for the original permutation rows, the numeric bounds on their pole weights, and their use in the large-aspect interlacing theorem.

An independent agent compared the signed identity and the complex pole-product estimate at `63c4e95` with the common-circle argument. The reviewer recovered the $n+1-k$ correction with positive sign and the $n+1$ correction with negative sign, checked both pole locations under inversion, and verified that normalized Fourier measure cancels the integral's factor of $2\pi$. The product estimate supplies the paper's products of first-order kernels. The differentiated kernels with squared denominators and the outer row normalization still require their own estimates. The reviewer checked the statements and derivation by inspection. [Comparison argument](../../fourier-circle/README.md)

The integral product estimate also has a specialization to the actual odd lattice, including the signed contrast multiplier and absolute convergence for every cutoff at least three. [Statement, proof and remaining obligations](lattice.md)

The differentiated kernel has a termwise angular derivative with an integrated bound in terms of the squared pole factors. [Differentiation and angular integral](derivative.md)

The differentiated contrast kernel satisfies the first-moment bound over the full odd lattice. Both integrations by parts now give coefficient inequalities under their stated inputs. [Coefficient errors and verification record](coefficient-errors.md)

The [small-height numerator contraction](numerator-small-height.md) gives the bound for the explicit odd-pole log series when the height is at most four times the square root of the cutoff.
