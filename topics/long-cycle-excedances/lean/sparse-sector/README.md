# Consecutive interlacing in the large-size sector

Let $E_{n,k}(t)$ enumerate permutations of $[n]$ by strict excedances, allowing only cycles of length at least $k$. The proposed formal theorem covers every pair of original sizes $n,n+1$ satisfying

$$
n\ge10000,\qquad k\ge8,\qquad 30\log n+20<\frac{n}{200k}.
$$

The reduced rows $E_{n,k}(t)/t$ and $E_{n+1,k}(t)/t$ have $n-2$ and $n-1$ simple negative roots. They strictly alternate, and the larger row supplies both ends. The original rows share a simple zero at the origin and interlace weakly. [Source conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Formal statement](RepositorySparseSector.lean)

The repository’s reviewed written argument already covers this sector and the other admissible sizes. Bowen Zuo also proved eventual interlacing at each fixed cutoff, with an existential size threshold. This package concerns formal coverage of the explicit joint inequality above. The all-size result remains 🟨 Partial · Lean 4. [Reviewed all-cutoff argument](../../all-cutoffs/README.md) · [Zuo’s fixed-cutoff theorem](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/releases/tag/v1.0.0)

## From coefficients to interlacing

Set $H=\lfloor7\sqrt n/20\rfloor$, $J=\lfloor\sqrt n/2\rfloor$ and $c_j=[t^j]E_{n,k}(t)$. The exterior intervals have centers $u_h=c_h/c_{h+1}$ for $1\le h\le H$. Normalizing $c_j$ by $j^n$ gives bounds for $u_h$ and both adjacent coefficient ratios. Bernoulli’s inequality then gives weighted geometric tails on either side of the two central monomials. The resulting separation $20u_h<u_{h+1}$ orders all intervals. Their upper edges lie below the first middle interval. [Tail calculations](coefficient-tails.md) · [Actual coefficient estimates and center cap](RepositoryOldFrontTails.lean) · [Ordering every pair](ExteriorScaleOrder.lean)

Let $V$ be the full lag polynomial in the insertion recurrence. At $j\le J$ the orbit-load calculation bounds $|[t^j]V|$ by $(8/25)c_j$, including rank zero. Beyond $J$ the bound $|[t^j]V|\le j^{n+1}$ combines with the same geometric decay. The two signed-polynomial tests now give each exterior root and the sign of the successor at that root. The middle-root signs, reciprocity and the degree counts assemble the two complete root lists. [Orbit-load estimates](../../color-load-bounds/README.md) · [Exterior tests](../front-envelope-sums/README.md) · [Middle witnesses](../middle-residues/README.md) · [Assembly](../front-middle-join/README.md)

## Verification

A fresh-context agent referee compared the proof with the original claim, traced all seven hypotheses of the exterior reduction, and checked the direction of the adjacent root lists. [Independent review](independent-review.md)

The final implication and the actual center-cap algebra passed local Lean 4.19 checks with the imported statements supplied as explicit hypotheses. A production run must build the entire composition from its imports on Lean 4.33.1, mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`, audit its axiom sets and replay the resulting modules. This build is pending. [Verification driver](../front-envelope-sums/check.py)

~~~sh
python3 -I topics/long-cycle-excedances/lean/front-envelope-sums/check.py /tmp/long-cycle-sparse-sector
~~~
