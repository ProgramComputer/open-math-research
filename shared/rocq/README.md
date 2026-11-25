# Shared Rocq library

These modules use Rocq 9.3.0 with its standard library. They belong to the logical namespace `OpenMath`.

| Module | Checked statements |
|---|---|
| [BoundedCompositions](BoundedCompositions.v) | Duplicate-free enumeration of integer points with given coordinate bounds and sum. Repeated finite differences give a counting formula for arbitrary bounds. |
| [FiniteDifferences](FiniteDifferences.v) | Coefficients of a count series multiplied by $(1-z)^k$, conversion from the binomial basis, and comparison between two denominator orders. |
| [PolynomialSeparation](PolynomialSeparation.v) | Evaluation of coefficient lists, invariance of negative zeros under a change in normalization, and a necessary root-separation condition for weak interlacing in either orientation. |

The [prism-splitting verifier](../../topics/prism-splitting/rocq/verify.sh) builds these modules in dependency order and kernel-checks the result that uses them.
