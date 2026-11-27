# An adjacent sine comparison for the bounded-aspect middle

Let $E_{m,k}(t)$ count permutations of $[m]$ by strict excedances with every cycle of length at least $k$. Fix $0<\theta\le\pi/2$, $S=\sin\theta$, $t=-\exp(-\pi\cot\theta)$ and $R=\pi/S$. Use the positive normalization $F_m=R^m E_{m,k}(t)/(m!(1-t)^m)$. The estimate holds for all integers $n\ge10000$, $4\le n/k\le48$, at every middle angle $nS^2\ge6/5$.

$$
\frac{k}{S}\bigl(\sin((n+1)\theta)F_n-\sin(n\theta)F_{n+1}\bigr)>\frac{291701}{10^6}.
$$

The estimate concerns the actual consecutive rows, including upper sizes at which a new cycle count becomes possible. It supplies another route to the middle step of the repository’s bounded-aspect proof. At a sample $n\theta=j\pi$ it gives $(-1)^jF_n>0$. At an old zero in $j\pi<n\theta<(j+1)\pi$ it gives $(-1)^{j+1}F_{n+1}>0$. Thus the intermediate value theorem selects signed old roots in all complete middle gaps. The exterior witnesses, odd central sign, reciprocity and the degree count complete the bounded-aspect root lists. [Alexandersson’s statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Reviewed bounded-aspect theorem](../paired-residues/README.md) · [Root-list assembly](../lean/front-middle-join/README.md)

For a pair of principal waves $F_m=a\cos(m\theta)+b\sin(m\theta)$ the sine comparison is exactly $aS$. For the actual rows, multiply their generating series by $1-2u\cos\theta+u^2$. Writing the resulting coefficients as $h_j$, the unscaled comparison is exactly $\sum_{j=0}^{n+1} h_j\sin((1-j)\theta)$. This finite identity retains cancellation between adjacent sizes. The estimates use the existing occupied-pole expansion and its absolute coefficient envelopes. They dispense with the angular derivative of the occupied product and the insertion lag at an old root. The small-angle carrier amplitude still uses the previously proved bound on the principal complex phase. [Small-angle proof](small-angle.md) · [Large-angle proof](large-angle.md) · [Exact scalar certificate](check-bounds.py) · [Output](bounds-output.txt)

A fresh-context agent independently derived the determinant and its boundary term and reran all sixteen slabs. The independent checker uses a different lattice cutoff and rounding precision and directly computes powers of the positive majorant. It gives the same lower bounds to six decimal places. [Independent review](independent-review.md) · [Independent checker](independent-check.py) · [Independent output](independent-output.txt)

A single principal-residue estimate now gives the stronger lower bound $322338/10^6$ throughout the same sector. It covers all angles, including the conjugate pole on the unit circle, and removes the earlier Poisson and differentiated-tilt estimates from the middle argument. [Uniform principal-residue proof and checks](uniform-carrier.md)

**Formal status: ⬜ None for the displayed uniform lower bound.** Local Lean 4.19 checks cover the telescoping identity, the signs at samples and old zeros, and the conditional root-list assembly with the exterior and degree theorems supplied as inputs. The quantitative pole estimates remain on paper with a rational checker. The all-size proof retains its separate verification record. [All-cutoff argument and scope](../all-cutoffs/README.md)

## Computational checks

From this directory, run

~~~sh
python3 -I -B check-bounds.py
python3 -I -B independent-check.py
python3 -I -B obstruction.py
python3 -I check-sine.py --output /tmp/long-cycle-sine-points.json
~~~

The three rational checks use the Python standard library. The first reruns nine large-angle and seven small-angle rational bounds. The obstruction checker shows why a direct absolute Cauchy estimate at the third pole fails at a specified boundary pair. The point checker uses python-flint 0.9.0 with 384-bit ball arithmetic. Its positive enclosures cover 30 points at the old sizes $n=mk-2,mk-1,mk$, where $m\in\lbrace5,11,20,32,48\rbrace$, $k=\lceil10002/m\rceil$ and $S\in\lbrace11/1000,3/100\rbrace$. The smallest enclosed scaled comparison exceeds $0.85867$. [All point enclosures](sine-points.json) · [Literal enumeration and interval code](check-sine.py)

The interval calculation uses an independent generating function. Set $G(u)=(1-t)/(1-t\exp(Ru))$. For $p\ge2$, the coefficient of degree $p$ of $\log G$ is the normalized contribution of one cycle of length $p$, by the Eulerian power-sum identity. Subtract all terms of degrees less than $k$ from $\log G$ and exponentiate to obtain the row series. This removes its degree-one term for every cutoff under consideration. Direct enumeration of labeled permutations checked both adjacent coefficients in each of 21 small pairs. The finite-angle enclosures are separate from the uniform rational certificate.

## Scope and provenance

Alexandersson asks for consecutive interlacing at all admissible sizes. This work concerns a bounded-aspect step of the repository’s existing all-size argument. It draws on the reviewed residue expansion, binomial envelopes for cycle probabilities, and signed odd-pole identity, including Bowen Zuo’s Eulerian-series formalization. Rakotoson and Rakotondrajao study the related associated Stirling Eulerian numbers and their generating functions. [Tracking issue and attribution](https://github.com/ProgramComputer/open-math-research/issues/4) · [Zuo’s source](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/EulerianSeries.lean) · [Rakotoson and Rakotondrajao, 2025](https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.html)

The November 27, 2026 method search used GitHub code search for “excedance” with “sine determinant”, a web search for “cycle length”, “interlacing”, “sine determinant”, and the authors’ names, and domain-restricted searches of arXiv, GitHub and indexed X posts for long-cycle excedance interlacing. GitHub code search returned no match for that phrase. Public indexing is incomplete, particularly for X. Priority for the sine estimate is undetermined.

The [reflected signed-pole estimate](reflected-carrier.md) proves two lower bounds for the entire principal product with eleven paired terms in each certificate.

The [nonprincipal value estimate](nonprincipal-value.md) reduces the full second error term to a finite bin sum and a first-moment calculation over the signed odd poles.

The successor degree shift gives a stronger factorial bound for the regular numerator contribution in three aspect intervals. [Proof and numerical comparison](regular-numerator.md)

The isolated cutoff jump splits into its exact single-primitive contribution and a sum over products with at least two primitives. [Cutoff-jump proof and exact bounds](cutoff-jump.md)

The symmetric-window proof joins all four errors and reduces the indicated numerical margin to nine explicit finite inequalities. [Conjugate-pole calculation and determinant assembly](four-error-assembly.md)
