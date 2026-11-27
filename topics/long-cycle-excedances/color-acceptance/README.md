# A Worpitzky transform for color-cycle acceptance

Fix a minimum cycle length $k\ge2$. Let $E_{n,k}(t)=\sum_s a_{n,s}t^s$ count admissible permutations by strict excedances. A color assignment is a function from the $n$ labels to $p$ labeled colors, together with a permutation of those colors. Accept the pair when each cycle of colors receives at least $k$ labels in total. A color may receive no labels. Let $B_{n,p}$ count the accepted pairs and put $C_{n,p}=B_{n,p}/p!$.

The exact identity is

$$
\sum_{p\ge0} C_{n,p}t^p=\frac{E_{n,k}(t)}{(1-t)^n}.
$$

The exponent $n$ records the number of directed edges in the label permutation. This identifies the relaxed acceptance probability used in the [exterior-root estimates](../effective-front.md) without imposing a condition on the two halves of the label set. The [large-size formal reduction](https://github.com/ProgramComputer/open-math-research/pull/275) needs uniform bounds on the resulting coefficients and on the insertion lag.

## Proof by marking directed edges

Take an admissible permutation $\sigma$ on $n>0$ labels with $s$ strict excedances. On each directed edge $x\to\sigma(x)$ place an ordered string of bars. Require at least one bar on each ascending edge. If there are $p$ bars in all, give them distinct names from the $p$ colors. Every cycle of $\sigma$ contains an ascending edge because its labels are distinct and its length is at least two. Reading from each bar to the next in a cycle gives a decreasing list of labels, possibly empty. Assign those labels to the first bar's color and send that color to the next bar's color. Every resulting cycle of colors receives exactly the number of labels of its original cycle, so the pair is accepted.

Conversely, in each cycle of an accepted color permutation, replace each color by its named bar followed by all labels of its class in decreasing order. Erase the bars to recover the label cycle and retain their positions along its directed edges. An accepted color cycle contains at least two labels, so erasing bars preserves every cycle. Any ascending edge passes a bar. Names distinguish successive bars even when their intervening class is empty. The two constructions are inverse.

For $p\ge s$, distributing the $p-s$ surplus bars over $n$ directed edges gives $\binom{n+p-s-1}{p-s}$ choices, followed by $p!$ assignments of color names. For $p<s$ the fiber is empty. Summing over $\sigma$ and using the binomial series proves the identity. For $n=0$ the only accepted pair has $p=0$, and both power series equal 1.

## Independent recurrence

Distinguish the color cycle containing the color of label 1. If it has $j$ colors and $m$ labels, choose the $j$ colors and the $m-1$ other labels. Order the colors cyclically in $(j-1)!$ ways and assign the $m$ labels to them in $j^m$ ways. On the remaining labels and colors use any accepted pair. Cancellation of the factorials gives

$$
C_{n,p}=\sum_{m=k}^n\binom{n-1}{m-1}\sum_{j=1}^p j^{m-1}C_{n-m,p-j}.
$$

For $m\ge2$, the classical Eulerian power-series identity gives $\sum_{j\ge1}j^{m-1}t^j=tA_{m-1}(t)/(1-t)^m$. Multiplying the color recurrence by $(1-t)^n$ yields the cycle-containing-label-1 recurrence of the original enumerator. Its one-cycle factor is $tA_{m-1}(t)$. This proves the identity a second way. Rakotoson and Rakotondrajao give the one-cycle factor as Theorem 5, equation (8), on printed page 4 and study the restricted rows. [Associated Stirling Eulerian Numbers and Their q-Analogues](https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.pdf#page=4)

## A rational probability bound

For $n,p\ge1$ put $f=C_{n,p}/p^n$, $\alpha=a_{n,p}/p^n$ and $\eta=n(1-1/p)^n$. Then

$$
0\le f-\alpha\le\min\left(1,\ 2\eta,\ \sum_{r=1}^p\eta^r\right).
$$

Indeed, a term with $r$ surplus bars uses $a_{n,p-r}\le(p-r)^n$, the labeled-run coefficient bound. The number $\binom{n+r-1}{r}$ of weak distributions is at most $n^r$, the number of ordered choices of $r$ edges. Bernoulli's inequality gives $(p-r)/p\le(1-1/p)^r$. Consequently the normalized contribution of this term is at most $\eta^r$. The gap is at most 1 since $f$ is a probability. If $\eta<1/2$ the geometric sum is at most $2\eta$, and otherwise $2\eta\ge1$. The bound includes $p=1$, where the gap vanishes. [Original coefficient bound in Lean](../lean/LongCycleRunColors.lean)

## Lean proof scope

The combinatorial proof enumerates actual word–permutation pairs and gives an equivalence at each choice of anchored label and color supports. The color permutation restricts to a transitive permutation of the distinguished color support and an arbitrary complement permutation. Counting these blocks, including singleton color supports, gives the tagged cardinal recurrence. Dividing by $p!$ supplies the normalized recurrence and the empty-input convention. [Executable acceptance type](ColorAnchor.lean) · [Anchored decomposition](ColorDoubleCount.lean) · [Tagged recurrence](ColorRecurrence.lean) · [Normalized recurrence](NormalizedColorRecurrence.lean)

The real count is bounded by $p^n$ because the tagged accepted pairs are a subset of all words times all color permutations. The repository adapter identifies this count with the binomial transform of the literal original rows and derives the $2\eta$ bound for every $n,p\ge1$, $k\ge2$. These estimates still need to be used to certify the exterior windows in the full interlacing proof. [Cardinality inequality](NormalizedColorBounds.lean) · [Literal transform and error](RepositoryColorCombinatorial.lean)

The combinatorial modules through the rational recurrence originally compiled with Lean 4.19.0 and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The immutable receipt records their original source hashes and axiom reports. The common-pin workflow checks the production modules and adapter with Lean 4.33.1 and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. [Lean 4.19 combinatorial receipt](combinatorial-lean419.txt) · [Real count receipt](real-bounds-lean419.txt) · [Common-pin runner](../lean/common-pin/check.py)

All four modules compiled and replayed on the frozen Lean 4.33.1 pin. The audit records the exact source hashes and axiom reports for 16 declarations. [Verification record](verification.txt) · [Common-pin check](../lean/common-pin/check.py)

The successor recurrence transports the actual polynomial insertion law to the color transform. Its marked-cycle convolution gives the exact successive difference and dominates the literal nonnegative lag coefficient. [Successor recurrence and lag comparison](successor.md)

## Verification and provenance

Run the following from this folder. The checker enumerates the word and the color permutation directly, erases the bars, checks injectivity, and compares each fiber size with stars and bars. It separately recomputes the anchored recurrence. All 140 triples with $0\le n\le6$, $0\le p\le4$ and $2\le k\le5$ passed, covering 180,248 accepted pairs. [Exact checker](verify.py) · [Output](finite-output.txt)

~~~sh
python3 -I verify.py
~~~

Bowen Zuo’s ordinary-descent release v1.0.0 at commit `e632c19bc246b819cd6b882cbf22c2fa9bc453de` already proves the occupancy representation for the literal excedance rows at positive row size and positive color count. The source expands the original enumerator divided by $(1-t)^n$ in `normalizedEnumerator_hasSum_orderedLabels` and identifies `originalLabelCoeff` with $p^n$ times the literal slot-permutation and ball-map success probability in `LongCycleBounds.Occupancy.original_eq_slot_probability`. [Zuo’s release](https://github.com/AlexZander-666/cycle-minimum-descent-real-roots/releases/tag/v1.0.0) · [Normalized enumerator](https://github.com/AlexZander-666/cycle-minimum-descent-real-roots/blob/e632c19bc246b819cd6b882cbf22c2fa9bc453de/formal/LongCycleBounds/InsertionBoundary.lean#L90-L93) · [Coefficient expansion](https://github.com/AlexZander-666/cycle-minimum-descent-real-roots/blob/e632c19bc246b819cd6b882cbf22c2fa9bc453de/formal/LongCycleBounds/GeneralCyclePositiveSeries.lean#L253-L258) · [Occupancy identity](https://github.com/AlexZander-666/cycle-minimum-descent-real-roots/blob/e632c19bc246b819cd6b882cbf22c2fa9bc453de/formal/LongCycleBounds/OccupancyVerified.lean#L142-L146)

The same release proves the marked one-label increment identities `weighted_label_jump_convolution` and `marked_probability_binomial_jump`. This package records an independent implementation of the color transform and its use in the exterior coefficient estimates. [Count increment](https://github.com/AlexZander-666/cycle-minimum-descent-real-roots/blob/e632c19bc246b819cd6b882cbf22c2fa9bc453de/formal/LongCycleBounds/OccupancyBinomialJump.lean#L111-L115) · [Probability increment](https://github.com/AlexZander-666/cycle-minimum-descent-real-roots/blob/e632c19bc246b819cd6b882cbf22c2fa9bc453de/formal/LongCycleBounds/OccupancyBinomialJump.lean#L143-L148)

An independent agent reconstructed the two counts and implemented the finite check. The power-series calculation uses classical Eulerian identities. Shareshian and Wachs studied barred ornaments and Eulerian quasisymmetric functions that retain cycle type and excedance data. The all-size interlacing proof still has partial formal coverage. [Eulerian quasisymmetric functions](https://arxiv.org/abs/0812.0764)
