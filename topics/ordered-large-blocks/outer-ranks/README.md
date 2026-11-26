# Uniform eventual interlacing at fixed outer ranks

Let $`O_{n,j}(t)`$ sum $`t^k`$ over all ordered partitions of $`[n]`$, with $`k`$ the number of blocks of size at least $`j`$. Write $`n=jm+s`$, $`0\le s<j`$. The degree is $`m`$, since $`m`$ blocks of size $`j`$ and $`s`$ singletons realize it, and the constant term is positive.

**Theorem.** For each integer $`H\ge1`$, there is a single old-size cutoff $`N_H`$ that works for every $`j\ge2`$. If $`n\ge N_H`$, the first $`H`$ available roots of each row $`O_{n,j}`$ and $`O_{n+1,j}`$ in decreasing modulus among all complex roots are simple and negative. Write $`a_r`$ and $`b_r`$ for the old and new moduli in that order. The following comparisons hold for $`1\le r\le H`$, with each comparison made when its indicated indices exist.

- At unchanged degree, $`a_r>b_r`$ and $`b_r>a_{r+1}`$.
- At the carry $`s=j-1`$, $`b_r>a_r>b_{r+1}`$.

The cutoff is existential. This result is about fixed outer ranks. Formal verification is ⬜ None. [Alexandersson’s conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Research issue #1](https://github.com/ProgramComputer/open-math-research/issues/1)

## Proof

When $`j,m\to\infty`$ and $`j/m`$ is bounded by a fixed constant, the [comparable-threshold proof](comparable.md) estimates the top coefficients at their positive saddles. The two neighboring terms at each fixed reciprocal balance give a Rouché count and the consecutive motion of the actual root. When $`j/m\to\infty`$, the [renewal proof](renewal.md) instead uses the positive short-block pole. Its coefficient-increment estimate preserves the direction of motion even when the matching roots are closer than the individual root errors. At the carry, the new reciprocal row has an extra leading constant and the old reciprocal coefficients shift by one index. The signed comparison controls the added constant and places the old root between the two specified new roots. Reciprocal moduli in these two proofs increase from the smallest upward, so taking reciprocals yields the inequalities above in decreasing original modulus. [Comparable-threshold review](review-comparable.md) · [Renewal review](review-renewal.md)

To obtain a single $`N_H`$, suppose there are failures with old sizes tending to infinity. Pass to a subsequence on which $`j`$ is constant or tends to infinity. In the constant case the [eventual fixed-threshold theorem](../all-fixed-thresholds.md) gives full strict interlacing, with the new root first in increasing modulus. Reversing the order gives the stated direction for each degree change. In the other case pass further so that $`m`$ stays bounded or tends to infinity. If $`m`$ is bounded, choose one fixed proportional window containing both $`n`$ and $`n+1`$. The [bounded-window theorem](../proportional-window.md) gives the full strict order for sufficiently large $`j`$, including degree zero or one and the last available index. When $`m\to\infty`$, pass to a subsequence with $`j/m`$ bounded by a fixed constant or tending to infinity. Apply the corresponding joint-growth theorem with $`H+1`$ ranks, so the adjacent comparator is available wherever required. Every subsequence case contradicts the failures.

The [rank-one carry refinement](carry.md) gives an asymptotic gap of $`m/(2j)`$ relative to the old largest root modulus under the stronger condition $`j/m^2\to\infty`$. Its [coefficient estimate](large-excess.md) also identifies why the fixed-threshold outer scaling changes in this regime. This quantitative refinement is separate from the independently reviewed order theorem.

## Exact checks

~~~sh
python3 -I -B check-enumerator.py
python3 -I -B check.py
~~~

The first compares the first-block recursion against an independent integer gap-product reconstruction for all 671 rows with $`2\le j\le12`$ and $`0\le n\le60`$. The second uses integer monomial dominance at rational radii to certify outer ranks on 24 sample pairs and bisects the certified brackets by exact signs. It certifies the first-rank comparisons for 18 pairs and the first two for four pairs. A reported **inconclusive** means that a dominance test failed or that the brackets did not establish the requested strict order. These finite tests are separate from the asymptotic proof. [Enumerator output](enumerator-output.txt) · [Rank-check output](check-output.txt)
