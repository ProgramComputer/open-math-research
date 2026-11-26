# Simple negative roots above quarter dimension

Let $`P`$ count labeled $`n\times d`$ binary matrices by their common column sum, with every row sum at most $`r`$. For $`n\ge10^6`$ and $`d\ge n/4`$, all but at most

$$
\left\lceil n\sqrt{\frac{\log(100n)}{2d}}\right\rceil+4
$$

of the $`\lfloor nr/d\rfloor`$ roots are proved simple and negative. At more than half as many columns as rows, coefficient separation gives the full degree of simple negative roots. The bound holds for every cap $`1\le r\le d`$. Each certified negative root lies in an annulus containing exactly one zero counted with multiplicity. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Manuscript](paper.pdf) · [LaTeX source](paper.tex)

For **one million rows, 250,000 columns and cap 127,000**, the polynomial has degree 508,000. At least **501,926 roots** are simple and negative. Exactly **500,000** lie strictly inside the unit disk and exactly **333,333** lie strictly inside the disk of radius $`2^{-250000}`$. All roots in both disks are simple and negative, and both boundaries are free of roots. A sharper binomial-tail check and a row-switching argument together isolate 502,482 simple negative roots, leaving 5,518 between the certified ranges. [Outer-root proof and exact counts](upper-edge/README.md) [Exact integer interval checker](verify.py) · [Earlier finite bounds on disk counts](../../../root-distributions/README.md)

At each covered central quota, seven consecutive unrestricted terms control the entire comparison circle. The cap changes those terms little enough that the rotated polynomial stays in the right half-plane. Near either endpoint a single term supplies the winding number. At three to four rows per column and under a stronger overflow bound the exact angular radius and every radius in its tilt bracket have the same certified count. [Independent root-count review](review.md) · [Angular radius proof and replay](angular-review.md) · [Prior angular comparison](https://github.com/ProgramComputer/open-math-research/pull/162)

**Formal verification**　⬜ None. Two independent agents reviewed the finite comparisons. Both Python checks use rational arithmetic. Run from this directory.

~~~sh
python3 -IB verify.py
python3 -IB verify-angular.py
tectonic paper.tex
~~~

The general real-rootedness conjecture remains open. The earlier below-cap comparison supplies an absolute-constant estimate on a broader range of dimensions. The theorem here gives an explicit error and height for every dimension at least one quarter of the height. The fixed-standard-deviation transition where the expected number of overflowing rows grows still lies beyond the finite argument. [Earlier comparison](../proof.md) · [Transition family and review](https://github.com/ProgramComputer/open-math-research/pull/169) · [Source and prior-work checks](../../../root-distributions/literature.md)
