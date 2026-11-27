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

## Verification

The research pin is Lean 4.19.0 at `6caaee842e94` and mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Each of the six source modules compiled locally. Their thirteen named axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`. The checker compiles in a fresh directory and verifies the named reports. [Source checker](check.py) · [Dependency manifest](../../../../shared/lean/lake-manifest.json) · [Hosted check](../../../../.github/workflows/long-cycle-fourier-contrast.yml)

```sh
cd shared/lean
lake exe cache get Mathlib.Analysis.Complex.CauchyIntegral Mathlib.Analysis.Complex.RealDeriv Mathlib.Analysis.SpecialFunctions.ExpDeriv Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus Mathlib.Tactic.FieldSimp Mathlib.Tactic.LinearCombination Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Tactic.Positivity
lake env python3 -I ../../topics/long-cycle-excedances/lean/fourier-circle/check.py
```

The verification still requires a specialization to the infinite signed pole sums for the original permutation rows, estimates of those sums, and their use in the large-aspect interlacing theorem.
