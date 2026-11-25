# Formal verification of the torus reduction

The [Lean 4 source](BalancedPairCompression.lean) proves that a distinct pair $x,y$ of complex unit numbers has a sum strictly inside the segment between the two equal-pair sums with the same product. For an objective $|a+b(x+y)|^2$ with $b\ne0$, one of those equal-pair endpoints strictly improves the objective. Thus a distinct maximizing pair forces $b=0$. This is the pair comparison in the proof of torus dominance. The checked statements include the case $x+y=0$.

The [finite-torus module](BalancedTorusMaxima.lean) preserves the exact coordinate product when a pair is replaced. It proves pair affineness for the sum of the first $r$ elementary symmetric polynomials. The [component theorem](BalancedTorusComponents.lean) proves that each connected component of the maximizers of the modulus of the actual balanced-array row polynomial on the fixed-product torus contains a diagonal point, also after scaling the coordinates by $t$. Its proof obtains the auxiliary maximum by compactness and connects pairs while keeping their product fixed.

**🟨 Partial · Lean 4.** The analytic root theorem also requires a comparison of diagonal phases, uniform integral estimates and a count of zeros at both ends. This release provides written proofs of those steps. [Paper](../fixed-rank-eventual.pdf) · [Kernel report](../verification.json)

From the [shared Lean project](../../../shared/lean/README.md) with the pinned dependencies, run

~~~sh
lake build BalancedTorusComponents
~~~

## The first zero at every row count

Lean checks injectivity on a closed complex disk under linear-coefficient dominance, nonvanishing of the formal derivative there, and the geometric comparison giving the bound $36/37$. The layer-count inequalities and the comparison of consecutive balanced-array rows have written proofs. Rebuild these supporting lemmas with `lake build OpenMathResearch.DiskUniqueness`. [Shared Lean source](../../../shared/lean/OpenMathResearch/DiskUniqueness.lean) · [All-row theorem](../first-root.md)
