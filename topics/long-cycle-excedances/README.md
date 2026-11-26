# Excedance zeros for permutations with long cycles

The uniform theorem gives one cutoff $N$ such that for every $n\ge N$ and every $3\le k\le n$, the nonzero roots are simple, negative and strictly interlace the next row at the same $k$. This leaves only finitely many pairs in the full conjecture. The proof gives no numerical $N$. [Uniform argument](uniform-interlacing.md) · [Independent review](review-uniform-interlacing.md)

For minimum cycle length $k=3$, the reviewed proof gives simple negative nonzero roots and strict interlacing between consecutive rows for every $n\ge3$. Both conclusions also hold for every $k\ge3$ and $n\ge Bk^2$ with one absolute constant $B$. The proof does not give its numerical value. [Uniform cutoff](quadratic-cutoff.md) · [Review](review-quadratic-cutoff.md) All $399$ coefficient vectors in the finite part for $k=3$ were reconstructed independently. The original conjecture still asks for all $n\ge k$ at every $k\ge4$. [Argument](fixed-threshold.md) · [Source and earlier work](LITERATURE.md) · [Alexandersson’s original statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances)

For all sufficiently large $n$, the proposed all-root theorem gives $n-2$ distinct negative zeros and a simple zero at zero whenever the minimum cycle length satisfies $k\ge 100n/\log n$. The bound is uniform over $k\le n$ and permits the maximum number of cycles to grow. [All-root theorem and proof](linear-cutoffs.md)

For each $3\le k\le n$, the proposed theorem gives a simple negative closest nonzero root, strictly between the closest and all the remaining nonzero-root moduli in the next row. Reciprocation gives the largest root. In every sufficiently large row, all ranks through $\lfloor\tfrac14\sqrt{n/\log n}\rfloor$ at either end alternate, uniformly in the minimum cycle length $k$. [Statement and argument](proof.md) · [Alexandersson’s conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsPermutations) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)

**⬜ None.** The arguments are written. Exact integer checks of the extreme-root theorem cover 465 rows and 435 consecutive pairs through size 32. Reproduce the [archive](prefix.jsonl.gz) from the repository root using Python 3.10 or later.

~~~sh
python3 -I -O topics/long-cycle-excedances/verify.py
python3 -I -O topics/long-cycle-excedances/verify_threshold_three.py
python3 -I -O topics/long-cycle-excedances/verify_cycle_deletions.py
~~~

An independent agent-assisted review checked the run encoding, the explicit formula for the second coefficient, the root separation in consecutive rows, and the uniform binomial probability estimate. The new threshold-three certificate supplies 39,800 disjoint dyadic brackets across the 399 rows. The second checker uses inclusion-exclusion on fixed points and transpositions. [Finite certificate](threshold-three-prefix.jsonl.gz)

The independent referee checked the analytic inequalities and reconstructed all 79,600 endpoint signs by clearing denominators. [Referee report](review-fixed-threshold.md) · [Independent sign checker](verify_endpoints.py) · [Manuscript](paper.tex)
