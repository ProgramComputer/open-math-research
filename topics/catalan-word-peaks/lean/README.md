# Lean check of the strict Catalan peak sign transfer

Lean defines the strict-peak counting polynomial directly by enumerating
Catalan words. Words have zero first letter and adjacent increases at most
one. The bound on each letter identifies the finite alphabet with the
original nonnegative-integer word definition. Strict peaks use three
consecutive letters with the middle letter strictly largest. [Alexandersson's conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjCatalanWordPeaks) · [Baril et al., definition and generating function](https://arxiv.org/html/2404.05672v1#S5.Thmtheorem1)

The unconditional combinatorial results are in [CatalanStrictPeaks.lean](CatalanStrictPeaks.lean).
Theorem `coeff_C` gives each coefficient as the cardinality of the set of
valid words with that peak count. Theorems `eval_zero_pos`, `leadingCoeff_pos`,
and `natDegree_C` give both endpoint signs and the degree
$\lfloor(n-1)/2\rfloor$, with natural subtraction for the empty word. The
degree bound pairs each peak start with its successor. The alternating
word $0101\cdots$ attains the bound.

The reusable [OrientedNegativeInterlace.lean](../../../shared/lean/OpenMathResearch/OrientedNegativeInterlace.lean)
uses the shared alternating-sign root lemmas for both degree patterns.
If the old positive root moduli in increasing order are $o_1,\dots,o_m$ and
the new ones are $v_1,\dots,v_d$, the output gives $v_i<o_i$ for every $i\le m$
and $o_i<v_{i+1}$ whenever $i+1\le d$. For a nonconstant old row, the new rightmost negative zero is farther right.
The old farthest modulus exceeds every new modulus in the equal-degree case.
With a degree increase, it lies between the final two new moduli.

[CatalanStrictPeaksInterlacing.lean](CatalanStrictPeaksInterlacing.lean) applies
the reusable result to the exact Catalan polynomial in two stages.

- `roots_from_checkpoints` takes the normalized phase with left
  value $1/4$ and right value $n/2-1/8$, an increasing positive modulus
  parametrization on the open interval, and the strict signs at integer phase
  levels $1\le k<\deg C_n$. Its proof constructs the ordered samples using
  continuity and uses the constant and leading signs to exhaust the degree.
- `next_from_old_root_signs` takes the complete increasing modulus list of
  the simple negative zeros of $C_n$ and the sign $(-1)^i$ of $C_{n+1}(-o_i)$.
  It concludes the directed strict interlacing and the full next root multiset.
- `interlacing_from_finite_and_analytic_signs` records the split at $n=150$.
  Its hypotheses include the strictly interlacing pairs for old rows $n<150$.
  For $n\ge150$ it takes the checkpoint package and the strict signs at
  every old root.

**Partial Lean verification.** Lean verifies the entire finite prefix,
identifies the analytic branch, and proves the coefficient formula as the
sum of the four improper ray integrals. It verifies radial moments and
integrated envelopes and applies them to the normalized near-ray mean under
the stated interior angle bounds. It bounds the actual normalized far-ray
contribution in both angular ranges and proves the successive-size bounds
for the near mean. The phase connection, small-angle real-part estimate and
strict sign comparisons remain in the written proof.

## Exact recurrence on heights and preceding ascents

The [recurrence module](CatalanStrictPeaksRecurrence.lean) proves that a
finite-state transfer computes the strict-peak polynomial for every word length.
A state has height $h$ and a Boolean recording the previous ascent. Appending
$x\leq h+1$ records the ascent $h<x$ and adds a peak exactly when the old
flag records an ascent and $x<h$. The proof bijects the extensions with the
new Catalan words and verifies the update of the peak count. The theorem
`enumerate_X_eq_C` identifies the transfer polynomial with the word
enumerator.

The executable function `coefficients n` returns the coefficient list in
increasing power order. It evaluates the recurrence once at
$q=(n+1)^n+1$, which exceeds the count in any coefficient. The theorem
`coefficients_get_eq_C` proves that integer digit extraction in this base
recovers each coefficient of the original polynomial. Each materialized row
contains two counts per height, and each step examines a quadratic number of
state pairs. The algorithm avoids enumerating the words.

The recurrence and coefficient recovery are kernel-checked at every length.
[Recurrence kernel output](recurrence-kernel.txt)

## First-return generating function and scaled discriminant

The [first-return module](CatalanStrictPeaksFirstReturn.lean) proves the
bijection $w=0(u+1)v$, with the suffix beginning at the first later zero
when present. Its exact peak-count formula includes the possible boundary
peak when the suffix is nonempty and the positive block is a singleton or
ends in a strict ascent. A peak-preserving final rise counts these blocks
by the shorter word family. The resulting coefficient convolution gives
`generatingFunction_eq` for the
[formal series](CatalanStrictPeaksGeneratingFunction.lean) of the original
polynomials. [Published generating-function identity](https://doi.org/10.26493/2590-9770.1794.fc5)

The [discriminant module](CatalanStrictPeaksDiscriminant.lean) checks that
the scaled series has coefficients $c^nC_n(1-c^{-2})$. It proves its quadratic
equation and constructs a formal square root, with constant term one, of
$(1+x^2)^2-4cx$ for $c\ne0$.
[Generating-function kernel output](generating-function-kernel.txt)

## Cut geometry and explicit majorants

The [geometry module](CatalanStrictPeaksCutGeometry.lean) factors the quartic
into its two conjugate pairs for $0<d<1$, shows that the near pair has strictly
smaller modulus, and rules out real branch points. It verifies the direct,
conjugate and opposite cross-pair coefficient bounds, including the strict
near denominator bound $|b_0|<3$. The
[parameter module](CatalanStrictPeaksCutParameter.lean) proves positivity
and strict angular ordering of $-t$ on the checkpoint interval.

The [pointwise bounds](CatalanStrictPeaksCutBounds.lean) verify the short
reciprocal and the three square-root product estimates in (4). They also
give the local integrand bound used in (5). The square-root factors are inputs
with their defining squares and nonnegative real parts. The
[moment arithmetic](CatalanStrictPeaksMomentArithmetic.lean) verifies the
rational bound in (5) after inserting the stated beta moments, and the
exponential comparisons in (6) and in the covariance tail. It uses exact
arithmetic at the first four lengths and an inequality for each step of four.

[Cut kernel output](cut-kernel.txt)

## Radial density and normalized moments

The [radial moment module](CatalanStrictPeaksBetaMoments.lean) uses the
substitution $s=x^{-1}-1$ in the integrals with weight
$\sqrt{s}/(1+s)^{n+1}$. It proves integrability and the product formula for
$M_j$ when $j+1/2<n$, the variance formula, and the tilt mean in (8).
The normalization ratio bound in (6) follows from monotonicity of
$n^2b(n)$ for integer $n$.

The module integrates the quadratic envelope in (5) and verifies the
$1/50$ and $1/(20n)$ tail bounds for the affine envelope in (6) and (11).
[Radial moment kernel output](beta-moments-kernel.txt)

## Analytic branch and Cauchy coefficient

The [analytic branch module](CatalanStrictPeaksAnalyticBranch.lean) takes the
product of the principal square roots associated with the four branch points.
It proves that the product squares to the quartic and has value one at zero.
The rationalized generating function is analytic on the domain with the four
radial cuts removed. The theorem `branch_at_scale` verifies the square-root
value $1-c^2$ at the removable pole $x=c$.

The theorem `analyticGenerating_hasFPowerSeriesAt` identifies the analytic
Taylor coefficients with $c^nC_n(1-c^{-2})$ by checking the same quadratic
equation and uniqueness in formal power series.
The theorem `analyticGenerating_cauchyCoeff` gives the coefficient as a
Cauchy integral on any circle centered at zero with positive radius less than
the distance to the nearest branch point. [Analytic branch kernel output](analytic-branch-kernel.txt)

## Finite-radius contour deformation

The [logarithmic strip module](CatalanStrictPeaksLogRoot.lean) extends the
principal square root continuously to the two edges of a logarithmic strip.
It checks the defining square on the closed strip, equality of the boundary
values inward of the branch point, and the jump $-2i\sqrt{s}$ beyond it,
where $s$ is the radial displacement divided by the branch point modulus.

The [contour summation module](../../../shared/lean/OpenMathResearch/LogarithmicContour.lean)
uses Cauchy–Goursat on rectangles and sums them so the two values at each
internal angle enter as a difference. The
[Catalan specialization](CatalanStrictPeaksRayTransfer.lean) constructs the
five successive angular sectors from the exact four branch points.
Its theorem `analyticGenerating_finiteDeformation` identifies
$c^nC_n(1-c^{-2})$ with the sum of the five outer arcs and the four signed
radial differences, with the Cauchy normalization $1/(2\pi i)$.
The starting radius can be any positive radius below the nearer branch
points and the outer radius can be at least as large as the starting radius.
The theorems `logSector_jump_zero` and `logSector_jump_sqrt` give the
two cases of each signed radial difference with its exact rational factor.

[Contour kernel output](ray-transfer-kernel.txt) · [Hosted replay](https://github.com/ProgramComputer/open-math-research/actions/runs/45743833834)

## Improper ray coefficient formula

For $0<d<1$, let $c=\mathrm{scale}(d)$ and let $\mathcal Z$ be the four cut
points. The theorem `analyticGenerating_fourRays` proves that for each
positive coefficient index $n$,
$$
c^n C_n(1-c^{-2}) =
-\frac{1}{\pi}\sum_{\zeta\in\mathcal Z}\zeta^{-n}
\int_0^\infty \sqrt{s}(1+s)^{-n-1}B_\zeta(\zeta(1+s))\,ds,
\qquad
B_\zeta(x)=-\frac{\prod_{\nu\in\mathcal Z,\ \nu\ne\zeta}\sqrt{1-x/\nu}}{2x(c-x)}.
$$
Each square root in $B_\zeta$ is principal. The theorem
`rayIntegrand_integrable` checks absolute integrability on all four rays.

The proof bounds the generating function uniformly at outer radii at least
two and sends the outer arcs to zero. Its substitution $s=e^x/|\zeta|-1$
for logarithmic radius $x$ supplies the Jacobian $(1+s)^{-1}$, giving the
factor $(1+s)^{-n-1}$ and the signed prefactor $-\zeta^{-n}/\pi$.
[Improper ray kernel output](improper-ray-kernel.txt) · [Hosted replay](https://github.com/ProgramComputer/open-math-research/actions/runs/45746699648)

## Normalized near-ray mean and tilt covariance

The [near-amplitude module](CatalanStrictPeaksNearAmplitude.lean) uses the
actual index-zero prefactor $B_z$ from the improper coefficient formula.
It proves the squares and positive real parts of the principal cut-factor
ratios and identifies the normalized integrand with the reciprocal and
three-factor product used in (4)–(6). Its theorem
`nearRay_integral_eq_mean` factors the integral into $B_z(z)b(n)J_n$.

The theorem `nearMean_close_to_one` proves $|J_n-1|<73/100$ for $n\ge150$,
$0<d<1$, $nd\ge2$, and $n\sqrt{1-d^2}\ge2$. The checked ray integrability
and the actual pointwise bounds supply the hypotheses for the integrated
envelopes. The theorem `nearMean_step_covariance` verifies (8) for every
positive $n$. `nearTiltCovariance_sub_const` proves that the amplitude
factor can be centered at its mean or at one. The connection between the
phase and the angle bounds remains to be checked.
[Near-amplitude kernel output](near-amplitude-kernel.txt)

The [near covariance module](CatalanStrictPeaksNearCovariance.lean) proves
`nearMean_step_lt_one_div`, the quantitative conclusion of (11), for
$n\ge150$, $1/2\le d<1$, and $n\sqrt{1-d^2}\ge2$. The bound $d\ge1/2$
includes the paper's small-angle sector. It also proves
`nearMean_step_lt_four_div`, the conclusion of (12), for $n\ge150$,
$0<d<1$, $nd\ge2$, and $n\sqrt{1-d^2}\ge2$. The proof centers the actual
conjugate root where $(1+s)^{-1}$ equals its radial mean. The signed
density changes sign at that point, so the conjugate root's secant
bound integrates to the difference of two exact first moments. The
local cubic and quadratic estimates and the affine tail bound cover
the rest of the covariance.
[Kernel audit](near-covariance-kernel.txt)

## Far-ray contribution

The [far-ray module](CatalanStrictPeaksFarRay.lean) bounds each of the actual
far-ray integrals by $(6/5)b(n)|B_w(w)|$ for $n\ge150$ and $nd\ge2$. The
pointwise comparison uses the three cut-factor norms and the increasing
distance from $c$ along the far ray. The endpoint calculation squares the
amplitudes and cancels the two shared cross-pair distances to bound
$|B_w(w)|\sqrt{\sin\theta}$ by $|B_z(z)|$.

The theorem `farRayError_abs_le` bounds the real contribution of the two
far-ray terms divided by $2a^{-n}b(n)|B_z(z)|/\pi$ by
$(6/5)a^{2n}/\sqrt{\sin\theta}$. The theorem `farRayError_smallAngle`
obtains the sharper $1/(100n)$ bound when $d\ge1/2$ and
$n\sin\theta\ge2$. The theorem `farRayError_largeAngle` obtains the
$1/25$ bound when $nd\ge29/10$ and $\sin\theta\ge7/10$. Its radial
power estimate uses six blocks in the binomial lower bound. The theorem
`farRayError_interior` gives the uniform $1/25$ bound when $nd\ge29/10$
and $n\sin\theta\ge2$. [Far-ray kernel output](far-ray-kernel.txt)

## Exact isolating intervals through length 150

The [packed coefficient checker](CatalanStrictPeaksFastCoefficients.lean)
uses the proved first-return convolution to certify the evaluation of every
row at $q=4^{150}+1$. This base exceeds each Catalan word count in the
prefix. Lean checks the successive convolution identities and recovers
all coefficients by base-$q$ digit extraction.

The [interval checker](CatalanStrictPeaksFinite.lean) certifies both signs
at the endpoints of every dyadic interval by comparing the positive and
negative terms with exact natural-number arithmetic. It checks the
within-row and consecutive-row interval order and uses the intermediate
value theorem and the exact degree to exhaust each root multiset.

The [prefix theorems](CatalanStrictPeaksPrefix.lean) prove that rows $0$
through $150$ have only simple negative zeros (`roots_through_150`) and
strictly interlace in the specified orientation for old row lengths
$0\le n<150$ (`interlacing_before_150`). The assertions about constant rows
are vacuous. `interlacing_from_analytic_signs` combines the checked prefix
with the analytic checkpoint and old-root sign hypotheses from length $150$
onward. [Prefix kernel output](prefix-kernel.txt) · [Hosted replay](https://github.com/ProgramComputer/open-math-research/actions/runs/45741075005)

To regenerate the candidate data from the repository root, run

~~~sh
python -I -O topics/catalan-word-peaks/code/make_lean_intervals.py \
  topics/catalan-word-peaks/results/family-rows.jsonl --last 150 --bits 72 \
  > topics/catalan-word-peaks/lean/CatalanStrictPeaksIntervalData.lean
~~~

[Written proof](../proof.md)

## Build

Run from the [shared Lean project](../../../shared/lean/README.md) with pinned
Lean and mathlib.

~~~sh
lake build OpenMathResearch.OrientedNegativeInterlace CatalanStrictPeaks CatalanStrictPeaksInterlacing
lake env lean -j1 ../../topics/catalan-word-peaks/lean/Axioms.lean
lake build CatalanStrictPeaksRecurrence
lake env lean -j1 ../../topics/catalan-word-peaks/lean/RecurrenceAxioms.lean
lake build CatalanStrictPeaksFirstReturn CatalanStrictPeaksGeneratingFunction CatalanStrictPeaksDiscriminant
lake env lean -j1 ../../topics/catalan-word-peaks/lean/GeneratingFunctionAxioms.lean
lake build CatalanStrictPeaksCutGeometry CatalanStrictPeaksCutParameter CatalanStrictPeaksCutBounds CatalanStrictPeaksMomentArithmetic
lake env lean -j1 ../../topics/catalan-word-peaks/lean/CutAxioms.lean
lake build CatalanStrictPeaksBetaMoments
lake env lean -j1 ../../topics/catalan-word-peaks/lean/BetaMomentsAxioms.lean
lake build CatalanStrictPeaksAnalyticBranch
lake env lean -j1 ../../topics/catalan-word-peaks/lean/AnalyticBranchAxioms.lean
lake build OpenMathResearch.LogarithmicContour CatalanStrictPeaksLogRoot CatalanStrictPeaksRayTransfer
lake env lean -j1 ../../topics/catalan-word-peaks/lean/RayTransferAxioms.lean
lake env lean -j1 ../../topics/catalan-word-peaks/lean/ImproperRayAxioms.lean
lake build CatalanStrictPeaksNearAmplitude
lake env lean -j1 ../../topics/catalan-word-peaks/lean/NearAmplitudeAxioms.lean
lake build CatalanStrictPeaksNearCovariance
lake env lean -j1 ../../topics/catalan-word-peaks/lean/NearCovarianceAxioms.lean
lake build CatalanStrictPeaksFarRay
lake env lean -j1 ../../topics/catalan-word-peaks/lean/FarRayAxioms.lean
lake build CatalanStrictPeaksPrefix
lake env lean -j1 ../../topics/catalan-word-peaks/lean/PrefixAxioms.lean
~~~

[Kernel output](kernel.txt)
