# Mixed root witnesses in Lean

The theorem `OpenMathResearch.LongCycleExcedances.interlace_of_mixed_root_witnesses` checks the separating-point step in the long-cycle excedance argument. It applies to real polynomials $P$ and $Q$ of degrees $m$ and $m+1$, with $P\ne0$, positive $Q(0)$ and positive leading coefficient of $Q$. In increasing positive modulus order, each of the $m$ disjoint closed windows $[l_i,u_i]$ is either a known old root or has opposite signs of $P(-x)$ at its endpoints. At both endpoints of window $i$ the sign of $Q(-x)$ is $(-1)^{i+1}$, where $i$ starts at zero. [Lean theorem](LongCycleMixedRootWitnesses.lean#L18) · [Intermediate certificate and argument](../intermediate/README.md#independent-separating-point-check)

The theorem gives complete ordered lists of simple negative roots of both polynomials. In modulus coordinates, the old root lies in its window and each complementary gap contains exactly one next root. The proof selects the old roots by the intermediate value theorem or the supplied point witnesses and exhausts the old degree. It applies the shared sign-transfer theorem to the two endpoint arrays. Uniqueness identifies the resulting complete next-root lists, so their inequalities hold simultaneously. [Shared sign transfer and root-list uniqueness](../../../shared/lean/OpenMathResearch/OrientedNegativeInterlace.lean)

This is supporting Lean coverage for [issue #4](https://github.com/ProgramComputer/open-math-research/issues/4). The row degrees, analytic bounds and finite certificate signs enter as hypotheses. The computation of the witness arrays and the full permutation interlacing theorem remain outside this build.

## Related formal proofs

Bowen Zuo’s strictly positive-width criterion also finds old roots by an endpoint sign change and locates next roots in the complementary gaps. The gamma-certificate readout instead accepts checked gamma rows and their bracket ordering. The mixed criterion uses old-root point witnesses alongside strict brackets and needs only the next-row values at their endpoints. [Zuo’s `interlacing_of_brackets`](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleFinite/Interlacing.lean#L80) · [Zuo’s `original_pair_of_gamma_checks`](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleFinite/K4Readout.lean#L8)

For the connection to permutations at general cutoff, Zuo’s `actual_general_cycle_row` identifies the original enumerator with $X$ times the general quotient. The shape and reciprocity of the quotient and the transfer back to the original enumerator are also formalized upstream. [Original-row identity](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/GeneralCycleQuotient.lean#L98) · [Quotient shape](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/GeneralCycleQuotient.lean#L131) · [Quotient reciprocity](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/GeneralCycleQuotient.lean#L159) · [Interlacing transfer](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/GeneralCycleQuotient.lean#L195)

## Build and axiom audit

The research build used Lean 4.19.0 (`6caaee842e94`) and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. With the pinned mathlib build cache available, run from the repository root. [Toolchain pin](../../../shared/lean/lean-toolchain) · [Dependency manifest](../../../shared/lean/lake-manifest.json) · [Shared Lean setup](../../../shared/lean/README.md)

```sh
cd shared/lean
mkdir -p .lake/build/lib/lean/OpenMathResearch
lake env lean -o .lake/build/lib/lean/OpenMathResearch/AlternatingSignRoots.olean \
  OpenMathResearch/AlternatingSignRoots.lean
lake env lean -o .lake/build/lib/lean/OpenMathResearch/OrientedNegativeInterlace.olean \
  OpenMathResearch/OrientedNegativeInterlace.lean
lake env lean -R ../../topics/long-cycle-excedances/lean \
  -o .lake/build/lib/lean/LongCycleMixedRootWitnesses.olean \
  ../../topics/long-cycle-excedances/lean/LongCycleMixedRootWitnesses.lean
lake env lean --stdin <<'LEAN'
import LongCycleMixedRootWitnesses
#print axioms OpenMathResearch.LongCycleExcedances.interlace_of_mixed_root_witnesses
LEAN
```

All three modules compiled. The audit reported `propext`, `Classical.choice` and `Quot.sound`.

## From an exact prefix to a whole-row sign

[LongCyclePrefixTail.lean](LongCyclePrefixTail.lean) checks the omitted-term estimate in the [intermediate certificate](../intermediate/README.md#certificate-in-each-intervening-gap). For the reduced row $P=E_{N,k}/t$, the coefficient at exponent $j$ is the coefficient at exponent $j+1$ of the original excedance polynomial. The certificate uses the bound $0\le [t^j]P\le(j+1)^N$. Given this bound on the omitted coefficients, Lean checks that the first $W$ coefficients approximate $P(-y)$ with error at most

$$
\frac{(W+1)^N B^W}{1-B((W+2)/(W+1))^N},
$$

for $0\le y\le B$ and a positive denominator. The comparison uses the decreasing ratio of the successive absolute term bounds and the existing finite geometric sum lemma. A strict signed prefix margin larger than this error proves the actual endpoint sign. The checked interval Horner rule also transfers a signed margin to the whole modulus window. Its multiplication bounds are for nonnegative moduli, as in the recorded certificates.

The declaration `interlace_of_prefix_and_mixed_witnesses` supplies the endpoint signs to the mixed root-list theorem above. It accepts exact old roots, whole-row signs already proved by other means, and prefix-certified signs in the same witness family. The canonical specialization below supplies the coefficient envelope for the original permutation rows. The row degrees and the analytic or finite data placing all the windows remain inputs. In particular the Lean proof has not replayed all the recorded windows of the reviewed result for $k\ge7$.

The example uses cutoff seven and sizes 14 and 15, which both admit two cycles. The dyadic endpoints are $6/65536$ and $7/65536$. Lean checks opposite old signs and a strictly negative next-row value throughout the window using four low coefficients. The [exact fixture reconstruction](check-cutoff7-fixture.py) separately obtains all 27 coefficients from the one- and two-cycle formulas and compares them to the Lean vectors. That reconstruction is an exact integer calculation. The pinned coefficient adapter below separately checks the general original-permutation identification and compares the same two coefficient vectors at runtime. [Fixture output](cutoff7-fixture-output.txt)

With the pinned research toolchain and mixed-witness objects above, run

~~~sh
cd shared/lean
lake build OpenMathResearch.DiskUniqueness
topic=../../topics/long-cycle-excedances/lean
lake env lean --root="$topic" -o .lake/build/lib/lean/LongCyclePrefixTail.olean "$topic/LongCyclePrefixTail.lean"
python3 -I -B "$topic/check-cutoff7-fixture.py"
~~~

The agent-assisted replay formed fresh objects for `AlternatingSignRoots`, `OrientedNegativeInterlace`, `LongCycleMixedRootWitnesses` and the new certificate module, reusing the pinned `DiskUniqueness` object. It used Lean 4.19.0 (compiler commit `6caaee842e94`) and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The six new audited declarations use only `propext`, `Classical.choice` and `Quot.sound`. This is supporting Lean coverage for issue #4. [Axiom output](prefix-tail-axioms.txt) · [Alexandersson’s original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances)

## The original coefficient envelope from decreasing runs

[LongCycleRunColors.lean](LongCycleRunColors.lean) proves that every coefficient of the original excedance enumerator satisfies

$$
0\le [t^p]E_{n,k}(t)\le p^n
$$

for every $k\ge2$. The Lean definition sums over permutations of the actual labels $\mathrm{Fin}(n)$. It counts strict excedances and applies the positive-return-time cutoff used in [Zuo’s pinned statement](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycles/Statement.lean). At cutoff at least two, the return-time condition excludes fixed points. The frozen Lean 4.33.1 archive was screened for the required coefficient envelope, a run-color encoding and an Eulerian or derangement comparison that would give the bound. The archive supplies the general row identity and shape cited above. This coefficient proof uses the pinned research environment.

The proof follows downward edges to the end of each decreasing run. It proves that two labels with the same run end are on a single descending path, because injectivity excludes two incoming edges. For a fixed-point-free permutation, the run ends are precisely the tails of its ascents. The image of each ascent is the largest label in its destination run. Thus the destination-run map is a permutation of the runs.

Tagging a permutation with a bijection of its $p$ run ends to $p$ colors yields a word on the original labels and a permutation of the colors. Lean proves that these two pieces recover the tagged permutation. A downward edge goes to the next smaller label in its color, and an upward edge goes to the largest label of the successor color. There are $p!$ labelings of the run ends. The checked injection into the product of words and color permutations gives the claimed bound after cancellation of $p!$.

The declaration `OpenMathResearch.LongCycleExcedances.RunColors.original_coeff_envelope` concerns the original permutation polynomial. The declaration `reduced_coeff_envelope` uses the identity $E_{n,k}=tP$ to give the bound $(j+1)^n$ at exponent $j$ of the reduced row. This supplies the coefficient-envelope input from the preceding section. The executable quotient bridge below shares its pin with the external quotient identity. Replaying all the required root windows remains open.

With Lean 4.19.0 (compiler commit `6caaee842e94`) and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`, run from the repository root

~~~sh
cd shared/lean
lake env lean ../../topics/long-cycle-excedances/lean/LongCycleRunColors.lean
~~~

The agent-assisted check compiled a fresh object and audited eight declarations. The audit reports subsets of `propext`, `Classical.choice` and `Quot.sound`. [Axiom output](run-colors-axioms.txt)

## Canonical reduced permutation rows

[LongCycleReducedRow.lean](LongCycleReducedRow.lean) defines the reduced polynomial
by shifting the coefficients of the original enumerator down one place.
For $n>0$ and $k\ge2$, the coefficient envelope at exponent zero gives
$[t^0]E_{n,k}=0$. Lean then proves $E_{n,k}=tP_{n,k}$ and that every
polynomial supplied by such a factorization equals $P_{n,k}$.

The checked declarations `canonical_signed_pos_on_window_of_horner` and
`canonical_interlace_of_prefix_and_mixed_witnesses` apply the sign and interlacing
criteria to these permutation rows. The coefficient bounds follow from the
decreasing-run theorem. The common-pin check below supplies the degree and endpoint
shape. The numerical margins and full root-list witness data remain inputs.

Zuo's frozen Lean 4.33.1 sources already provide the all-cutoff
[cycle quotient identity](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/GeneralCycleQuotient.lean#L98)
and the [insertion recurrence](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/UniversalRecurrence.lean).
The research check uses Lean 4.19.0 (compiler commit `6caaee842e94`) with mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. The uniqueness theorem applies to a
quotient of the same enumerator once the external factorization is available on
a common pin, as in the bridge below.

After preparing the mixed-witness and prefix-tail objects as above, run from
`shared/lean`

~~~sh
topic=../../topics/long-cycle-excedances/lean
lake env lean --root="$topic" -o .lake/build/lib/lean/LongCycleRunColors.olean "$topic/LongCycleRunColors.lean"
lake env lean --root="$topic" "$topic/LongCycleReducedRow.lean"
~~~

The four declarations report only `propext`, `Classical.choice` and `Quot.sound`.
[Axiom output](reduced-row-axioms.txt)

The [executable coefficient adapter](pinned-quotient/README.md) checks the
identification with the original permutation enumerator in Zuo's pinned Lean
4.33.1 environment. Its runtime check matches both cutoff-seven coefficient
vectors. The [rational endpoint bridge](common-pin/README.md) compiles the
research sign theorem and the pinned coefficient identity on the same Lean
4.33.1 setup. It verifies the shape of the original reduced row and certifies
each signed value from the corresponding rational margin.


## Continuous phase crossings

[LongCyclePhaseWindows.lean](LongCyclePhaseWindows.lean) checks the
nonmonotone phase selection used in the [aspect-20 join](../aspect-20/README.md)
and [uniform comparison](../effective-uniform.md). For each rising pair
of target levels, it selects the last lower hit before the first upper
hit. The selected old zero lies in the open phase band. For increasing
parameters and increasing moduli, the singleton windows are strictly
ordered and their moduli are strictly above the entrance modulus and below one.

For the aspect-20 join the offset is the number of exterior witnesses
and the phase levels start at rank `H + 1` and end at rank `n / 2`
with natural-number division. This gives `n / 2 - H - 1` singleton windows.
Use `H + 2` as the old sample parity when the cosine estimate is for the
original enumerator. Removing the factor of the variable reverses its
sign at negative arguments. The next
sign is required only at old zeros in the given open phase band. The
[bounded-aspect estimates](../bounded-aspect/grouped-proof.md) give the
sign inputs in the integer-angle case. The numerical phase bounds,
normalization and exterior-to-middle separation for the actual analytic
functions remain inputs.

The shared first- and last-hit lemmas and the window theorem compile
with the research pin, Lean 4.19.0 (compiler commit `6caaee842e94`) and mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. From the repository root, run

~~~sh
cd shared/lean
lake build OpenMathResearch.FirstLevelHits OpenMathResearch.AlternatingSignRoots
lake env lean ../../topics/long-cycle-excedances/lean/LongCyclePhaseWindows.lean
~~~

The three new theorems report only `propext`, `Classical.choice` and
`Quot.sound`. The [hosted 4.33.1 check](https://github.com/ProgramComputer/open-math-research/actions/runs/45926344480)
compiled and replayed both phase modules on the common pin.
[Audit excerpt](phase-windows-audit.txt)
