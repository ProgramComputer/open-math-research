# Fourier numerator contraction for cutoffs eight and nine

At $k=8,9$, the original finite log numerator at an outer point and at the principal pole differs from the corresponding two contracted analytic log values by a sum of norms less than $65$. The radius band is $r\le R\le(1+1/k)r$, with $r=|s+i\pi|$ and $s\ge0$. The conclusion includes $s=0$. [Original numerator theorem](RepositoryEightNineNumerator.lean)

For $s\le8\sqrt{k}$, the normalized reciprocal sine scale is at most $13/5$. The radial slope remains $5/2$ because $e-e^{-1}+1/7<5/2$. The proof uses the original finite coefficients and the identified disk logarithm.

For $s>8\sqrt{k}$, use $d=78/1000$, $q=101/100$, split $2$, and decay $3/20$ in the positive-frequency estimate. The narrowest denominator is $8(3/20)-(d+q)=14/125>0$. The exponent estimates $e^{272/125}\le9$ and $e^{39/250}\le6/5$ give the strict total bound below $65$. [High-height adapter](EightNineHigh.lean) · [Rational constants](EightNineConstants.lean)

On the pinned Lean 4.33.1 toolchain, the checker builds the shared small-cutoff proof and replays the cutoff-eight and cutoff-nine modules.

```sh
python3 -Bu topics/long-cycle-excedances/lean/fourier-eight-nine/check.py /tmp/eight-nine-numerator
```
