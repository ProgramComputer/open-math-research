# Endpoint signs from packed coefficients

For a permutation cutoff $k\ge2$ and size $n\le1001$, the checked theorem reads the sign of the original reduced row at $-p/D$ from a list of packed coefficients. It requires two checks on the supplied integers. Each decoded coefficient must equal the corresponding value of the rounded insertion recurrence, and the endpoint inequality must hold. The sign includes the contribution of all degrees.

Positive Horner evaluation rounds up and bounds the coefficient uncertainty. Alternating Horner evaluation rounds down at each multiplication and its absolute error is at most two for $0\le p/D\le 1/2$. The strict integer margin pays both errors and the omitted high-degree tail. The existing storage model and the mathematical coefficient bound supply the link to the literal labelled permutations. [Original-row theorem](RepositoryPackedPoint.lean) · [Integer endpoint test](CompactPoint.lean) · [Horner estimates](PositiveCeilHorner.lean) · [Coefficient enclosure](../compact-rows/README.md)

The complete source package targets Lean 4.33.1 and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The combined build passed all 32 printed axiom audits and all nine relevant module replays. The initial port needed an explicit cast for the dyadic ceiling denominator. [Hosted record](hosted-audit.txt) · [Independent scope review](independent-review.md). Individual packed row and endpoint witnesses require separate kernel checks. [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)

```sh
python3 -Bu topics/long-cycle-excedances/lean/packed-endpoints/check.py /tmp/packed-endpoint-build
```
