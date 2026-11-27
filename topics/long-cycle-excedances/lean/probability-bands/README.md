# Uniform bounds for the cycle probabilities

For cutoff $`k`$, write $`d_r=E_{r,k}(1)/r!`$. This is the probability that a uniform permutation on $`r`$ labels has every cycle of length at least $`k`$. The bounds used for the high-angle estimates are

| Cutoff | Sizes | Bound |
|---|---|---|
| $`k\ge13`$ | $`r\ge2k`$ | $`k d_r\le61/100`$ |
| $`k\ge22`$ | $`r\ge2k`$ | $`k d_r\le59/100`$ |
| $`k\ge100`$ | $`r\ge2k`$ | $`k d_r\le4/7`$ |
| $`k\ge2`$ | $`r\ge3k`$ | $`k d_r\gt547/1000`$ |

These are scalar ingredients of the written interlacing argument. They do not establish a high-angle sign or a result about the original root lists. [Degree-block argument](../../degree-blocks/README.md) · [Bounded-aspect argument](../../bounded-aspect/grouped-proof.md) · [Intermediate high-angle estimates](../../bounded-aspect/high-251.md)

The checked abstract recurrence has $`d_0=1`$, vanishing values at sizes strictly between zero and the cutoff, and

$$
r d_r=\sum_{i=0}^{r-k}d_i\qquad(r\ge k).
$$

Subtracting adjacent recurrence equations expresses the next scaled probability as a convex combination of a predecessor and a lagged value. Upper and strict lower bounds therefore propagate from a block of length $`k`$. On the second block, one-sided harmonic bounds follow by telescoping the logarithm and bounding it by its tangent. Fifth-degree exponential truncations certify all three rational upper constants. On the third block, the harmonic sum is at least $`\log 2`$ and the preceding lower bound is one half. This proves the stronger strict lower bound $`548/1000`$ as well. [Band proofs and factorial normalization](CycleProbabilityBands.lean)

The polynomial normalization first evaluates the exact anchored-cycle support recurrence at one. The factor of $`(a-1)!`$ counts the possible cycles on a chosen support of size $`a`$. Dividing by the factorial of the row size and reindexing the complementary size produces the displayed recurrence. The literal adapter uses Bowen Zuo's frozen v1.2.0 enumerator, Eulerian polynomial definition, and anchored recurrence. This is the original unweighted permutation probability, with the same strict minimum cycle length as the excedance conjecture. [Polynomial normalization](AnchoredProbability.lean) · [Literal adapter](RepositoryProbabilityBands.lean) · [Supplying pinned recurrence](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/AnchoredRows.lean#L158)

Use Lean 4.33.1 on the supplying mathlib pin `0df444a360eaa60ab8c11dca51a86af692955474` for the literal adapter. The runner authenticates the frozen source archive and dependency manifest. It can reuse the prior verified import archive or compile the required upstream closure in a new directory.

~~~sh
python3 -Bu topics/long-cycle-excedances/lean/probability-bands/check.py /tmp/probability-bands
~~~

The hosted run compiled and replayed all three modules on the supplying pin. It audited the normalization and original probability declarations using only standard axioms. [Hosted audit receipt](hosted-audit.txt) · [Runner log](https://github.com/ProgramComputer/open-math-research/actions/runs/45925747252/job/140266532063)
