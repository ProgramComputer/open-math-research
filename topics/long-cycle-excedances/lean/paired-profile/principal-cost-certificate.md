# Nine-slab principal-cost certificate

For each slab, let $l_b$ be the outward-rounded value from the [linear table](../sine-comparison/LinearSlabs.lean). With $G=2^{56}$ and $q_0=G$, use the outward-rounded recurrence

$$
q_b=\left\lceil\frac{\sum_{i=1}^b i l_i q_{b-i}}{bG}\right\rceil
\qquad(1\le b\le240).
$$

The [array implementation](RoundedProductTable.lean) proves this recurrence and its exact agreement with the mathematical sequence. The [cost module](PrincipalCostTable.lean) defines the rational principal cost and its millionth ceiling. The [original-enumerator adapter](PrincipalCostBridge.lean) supplies the recurrence to the [principal head and tail bound](RepositoryPrincipalSlab.lean), and bounds the original principal error by the computed ceiling. Its proof uses the same bin index and centered error as the analytic bound, including the $1/10000$ tail allowance.

| Slab | Upper bound in millionths |
| --- | ---: |
| 4–6 | 72559 |
| 6–10 | 12006 |
| 10–16 | 643 |
| 16–22 | 104 |
| 22–28 | 101 |
| 28–34 | 101 |
| 34–40 | 101 |
| 40–44 | 101 |
| 44–48 | 101 |

The [paired-profile replay](check.py) checks the Lean declarations and exports the 2169 linear values, all 2169 product values and the nine ceilings. The [independent arithmetic comparison](check-principal-cost.py) rebuilds the product values with integer quotient and remainder, recomputes the ceilings in exact rational arithmetic, and compares both full sets of outputs with Lean. These fixed numerals have an executable arithmetic replay. The logical bound uses the exact computable ceiling as its conclusion. In the local Lean 4.19.0 pilot, directly reducing even the first fixed numeral in the kernel exceeded the 60-second process cap.

The earlier [carrier checker](../../sine-comparison/check-carrier.py) supplies the slab list and target ceilings. Other determinant costs and the full interlacing conjecture are outside this certificate.
