# Simple negative outer roots from row deficits

Let $`D=\lfloor nr/d\rfloor`$ be the degree of the balanced-array polynomial with $`n`$ rows, $`d`$ columns and row cap $`r`$. If $`n\ge d`$, $`d`$ tends to infinity and $`\min(r,d-r)\ge\beta d`$ for a fixed $`\beta>0`$, at least a constant times

$$
\min\lbrace d,(n^2/d)^{1/3}\rbrace
$$

of its largest roots by absolute value are simple and negative. The constant depends only on $`\beta`$. At $`n=d^2`$, for example, the theorem isolates at least $`\lfloor d/16\rfloor`$ outer roots whenever $`d\ge16`$ and $`d/4\le r\le3d/4`$. The original conjecture asks for all roots at every admissible size. [Alexandersson’s conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Proof](paper.pdf) · [LaTeX source](paper.tex)

The proof counts the ways to add a one to a column. Two rows can exchange one unit of unused capacity. Comparing the counts before and after that exchange bounds the number of available rows. A distinguished extra row makes all column margins equal during the comparison. Theorem 1 turns the resulting estimates into a finite rational test with the two hypotheses $`X<1`$ and $`dH/(B+H)>\log 9`$. A simpler sufficient condition for $`n\ge d\ge4`$ and an internal quota $`k`$ uses only the total unused capacity $`e=nr-dk`$:

$$
256e(1+e/n)^2\le d\min(r,d-r).
$$

## One million rows

For $`n=10^6`$, $`d=250000`$ and $`r=127000`$, the degree is 508,000. The inner test isolates the first 502,387 roots in order of absolute value. Row switching isolates the last 95. Thus **502,482 roots are simple and negative**, and **5,518** remain in the intervening annulus, counted with multiplicity. The next inner quota fails this particular binomial-tail test. The types of the intervening roots remain open. [Interior theorem](../README.md) · [Exact counts](verify.py)

**Formal verification**　⬜ None. An independent agent-assisted argument also led to the middle-cap estimate for at least quadratically many rows. The mathematical review was agent-assisted. The independent reviewer checked the switching argument, the dimension ranges and the two numerical endpoints. A separate enumerator checks the extension identity and the row-availability estimates on 84 feasible small cap and margin combinations. [Review](review.md) · [Direct enumerator](verify-profiles.py) · [Source and scope](literature.md)

Run from this folder using Python 3 with its standard library. Tectonic rebuilds the manuscript.

~~~sh
python3 -IB verify.py
python3 -IB verify-profiles.py
tectonic paper.tex
~~~

A subsequent [research note on row-deficit monotonicity](monotonicity/README.md) gives an exact obstruction to extending the switching bound by global monotonicity of the excess number of available rows.

The [marked-row comparison](../marked-row/README.md) now certifies the first 506,470 simple negative roots in this example. Together with the last 95 from row switching, this leaves 1,435 roots in the intervening annulus.
