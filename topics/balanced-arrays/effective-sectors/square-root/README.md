# Effective square-root dimension at near-full row capacity

Let $`P(q)`$ count labeled $`n\times d`$ binary matrices by their common column sum, with every row sum at most $`r`$. For integers $`n\ge1`$, $`d\ge2`$ and $`1\le r\le d`$, the polynomial has exactly $`\lfloor nr/d\rfloor`$ distinct negative roots whenever

$$
d^2\ge16384\thinspace{}n\log(n+1),\qquad 50n(d-r)\le29d^2.
$$

The logarithm is natural. With $`n=m^3`$, $`d=m^2`$ and $`m\ge10^6`$, the result permits every integer corank $`d-r\le 29m/50`$. This supplies an effective threshold in a range missed by the earlier explicit bound $`d\ge4n/\log n`$. The general conjecture remains open. [Original statement by Alexandersson](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Previous near-full-cap bound](../sector-logarithmic.md)

The proof compares the capped polynomial with the unrestricted one on circles drawn between successive root moduli. At the $`i`$th midpoint, the variance of the tilted column sum is at most $`72(n-i)/d`$ in the comparison range. This controls the loss from the cap. Near the top quota, a single coefficient dominates on each of a second family of circles. The root counts themselves order the two families at their join. [Manuscript](paper.pdf) · [LaTeX source](paper.tex) · [Midpoint review](review.md) · [Review of the wider cap range](refinement-review.md) · [Sources and status](literature.md)

**Formal verification**　⬜ None. An independent agent reconstructed both versions of the argument, including the estimates at the joining index. The exact arithmetic script checks the numerical constants and the example degree.

Run from this folder.

~~~sh
python3 -B verify-constants.py
tectonic paper.tex
~~~
