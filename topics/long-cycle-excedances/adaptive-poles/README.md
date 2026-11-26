# Simple negative roots and strict interlacing from size 4,062,720

Let $E_{n,k}(t)$ count permutations of $[n]$ by excedances subject to each cycle having length at least $k$, and put $P_n(t)=E_{n,k}(t)/t$. For every $n\ge4{,}062{,}720$ and every $3\le k\le n$, the roots of $P_n$ and $P_{n+1}$ are simple, negative and strictly interlace at the same $k$. This gives an explicit sufficient range for Alexandersson’s conjecture. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#permutations-with-long-cycles) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)

The [full-minimum-powers estimate](full-powers.md) keeps the first $k-1$ powers at every occupied pole and handles the two-pole derivative before using an exponential bound for higher orders. The [degree-split estimate](degree-split.md) retains additional powers at the distinguished pole when the other numerator degrees are short. It bounds the derivative of a non-distinguished pole using the first numerator moment before summing that degree. Both estimates bound the actual and opposite insertion signs. For instance, the first aspect interval $4\le n/k\le5$ requires only $n\ge10{,}000$ after the exterior join.

## The uniform cutoff

For $n\ge250000^2$, use the previous uniform result. For the rows below that height and at least $4{,}062{,}720$, thresholds $3\le k<400$ are covered by the small-threshold circle lemma. When $k\ge400$ and $n/k<4$, use the complete three-cycle theorem, since the integer old row size is then at most $4k-1$. [Previous uniform theorem](../radial-taylor.md#combining-the-two-ranges) · [Small-threshold lemma](../small-threshold-circle.md) · [Three-cycle theorem](../three-cycle-complete.md)

In the remaining range write $x=n/k\ge4$. Apply the [adaptive table](degree-split.md) when $x$ is at most the boundary in its row below. At and above that boundary, the [wider-circle comparison](../radial-taylor.md) applies, since every listed logarithm bound gives $89x/100>47+(5/2)\log n$. The table gives the adjacent upper and lower ranges at their exact endpoints.

| Old row size | Aspect boundary | Upper bound for $\log n$ |
| --- | ---: | ---: |
| $4{,}062{,}720\le n<4{,}408{,}334$ | 96 | $15.3$ |
| $4{,}408{,}334\le n<7{,}500{,}000$ | 100 | $16$ |
| $7{,}500{,}000\le n<250000^2$ | 125 | $25$ |

The circle comparisons concern the actual next row. Thus the combined theorem asserts strict interlacing for that row throughout the stated range. The bounded-aspect estimates also certify the opposite insertion sign in their stated ranges.

## Verification

**Formal verification** ⬜ None. The continuous-angle comparison and degree count are written arguments. The checkers use exact rational arithmetic for the lattice sums, the scalar joins and the small-threshold constants. The interval records contain the accepted thresholds and row cutoffs. [Full-powers record](full-powers-output.txt) · [Degree-split record](degree-split-output.txt) · [Small-threshold replay](small-threshold-output.txt)

Run from the repository root with Python 3.10 or later and without optimization. The degree-split and small-threshold checkers import a sibling module.

~~~sh
python3 -I -B topics/long-cycle-excedances/adaptive-poles/check_full_powers.py
python3 -B topics/long-cycle-excedances/adaptive-poles/check_degree_split.py
python3 -B topics/long-cycle-excedances/verify_small_threshold_circle.py
~~~

[Full-powers independent review](review-full-powers.md) · [Refinement and small-threshold independent review](review-degree-split.md) · [Earlier radial review](../review-radial-taylor.md)

The unrestricted finite region below this cutoff remains open where other sufficient results do not apply.
