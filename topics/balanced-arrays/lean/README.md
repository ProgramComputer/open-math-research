# Formal verification of the fixed-product pair argument

The [Lean 4 source](BalancedPairCompression.lean) proves that a distinct pair $x,y$ of complex unit numbers has a sum strictly inside the segment between the two equal-pair sums with the same product. For an objective $|a+b(x+y)|^2$ with $b\ne0$, one of those equal-pair endpoints strictly improves the objective. Thus a distinct maximizing pair forces $b=0$. This is the pair comparison in the proof of torus dominance. The checked statements include the case $x+y=0$.

**🟨 Partial · Lean 4.** The analytic root theorem also requires a comparison of diagonal phases, uniform integral estimates and a count of zeros at both ends. This release provides written proofs of those steps. [Paper](../fixed-rank-eventual.pdf) · [Kernel report](../verification.json)

From the [shared Lean project](../../../shared/lean/README.md) with the pinned dependencies, run

~~~sh
lake build BalancedPairCompression
~~~
