# The prism-slice counterexample in Rocq

**🟩 Full · Rocq for $a=6$.** At level six, split the final bound of $(1^{10},2)$ to obtain $(1^{12})$. The two Ehrhart numerators fail to interlace in either orientation, even when ties are allowed. This single case disproves the splitting clause of Ferroni–McGinnis Conjecture 5.12. For the full family $a\ge6$, Rocq covers the endpoint and Lean covers every parameter. [Original conjecture, §5](https://doi.org/10.4153/S0008414X24000233) · [Topic and full family proof](../README.md)

## What Rocq proves

1. At dilation $t$, the candidate points are integer coordinate lists satisfying $0\le x_i\le t c_i$ and $\sum_i x_i=6t$. All coordinates are nonnegative, so a list of natural numbers represents each integer point uniquely. Rocq proves that the enumeration contains exactly these lists, has no duplicates, and has length equal to the count recurrence. [Enumeration and proof](../../../shared/rocq/BoundedCompositions.v)
2. For **every** $t\ge0$, a proved finite-difference formula evaluates those counts. The resulting identities identify every coefficient of both power series, with denominator orders 11 and 12. The coefficient vectors are checked by polynomial identities over the integers. [All-dilation identities and vectors](PrismEndpoint.v) · [Formal series operations](../../../shared/rocq/FiniteDifferences.v)
3. The split numerator $Q$ has a zero in $(-840,-838)$ and another in $(-57,-56)$. Exact endpoint signs and the real intermediate value theorem prove both claims. A positive Bernstein expansion proves $P(x)>0$ throughout $(-840,-56)$. Every weakly alternating pair of complete real-root lists requires a zero of $P$ between those two zeros of $Q$. [Sign certificates and disproof](PrismDisproof.v) · [Formal separation condition](../../../shared/rocq/PolynomialSeparation.v)

The theorem `prism_split_disproof` quantifies over every exponent used to normalize either lattice-count series by a power of $(1-z)$. At a negative argument, changing that exponent preserves the zeros of any resulting polynomial. This makes the obstruction independent of an affine-dimension calculation. The corollary `explicit_split` supplies both polynomials and their complete series identities with no hypotheses.

## Reproduce the verification

Install Rocq 9.3.0 and its standard library, and run this from the repository root.

~~~sh
topics/prism-splitting/rocq/verify.sh
~~~

The script builds the modules in a fresh temporary directory, prints the kernel assumptions of the main statements, and runs `rocq check` on the compiled disproof. The enumeration and full series identities are closed under the global context. The real-root argument uses three standard-library assumptions for classical real analysis. The verification record names all three and identifies the checked source files by SHA-256. [Audit declarations](Audit.v) · [Verification record](verification.json)
