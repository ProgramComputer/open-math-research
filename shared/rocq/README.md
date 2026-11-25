# Shared Rocq library

These modules use Rocq 9.3.0 with its standard library. They belong to the logical namespace `OpenMath`.

| Module | Checked statements |
|---|---|
| [BoundedCompositions](BoundedCompositions.v) | Duplicate-free enumeration of integer points with given coordinate bounds and sum. Repeated finite differences give a counting formula for arbitrary bounds. |
| [FiniteDifferences](FiniteDifferences.v) | Coefficients of a count series multiplied by $(1-z)^k$, conversion from the binomial basis, and comparison between two denominator orders. |
| [PolynomialSeparation](PolynomialSeparation.v) | Evaluation of coefficient lists, invariance of negative zeros under a change in normalization, and a necessary root-separation condition for weak interlacing in either orientation. |
| [BoxReflection](BoxReflection.v) | Integer-point reciprocity and reversal of numerator coefficients for boxes with unit and double bounds. |
| [NumeratorTable](NumeratorTable.v) | Finite numerator support and both leading coefficients from interior counts. |
| [PositiveSeries](PositiveSeries.v) | Positivity on $(0,1)$ for the numerator of a nonnegative count series with positive constant term. |
| [MonicRoots](MonicRoots.v) | Complete real factorizations, Vieta’s root sum, and an obstruction to weak interlacing that allows arbitrary leading scalars. |

The [prism-splitting verifier](../../topics/prism-splitting/rocq/verify.sh) builds these modules in dependency order and kernel-checks the result that uses them.
