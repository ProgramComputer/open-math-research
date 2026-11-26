# Excedance zeros for permutations with long cycles

For all sufficiently large $n$, the proposed all-root theorem gives $n-2$ distinct negative zeros and a simple zero at zero whenever the minimum cycle length satisfies $k\ge 100n/\log n$. The bound is uniform over $k\le n$ and permits the maximum number of cycles to grow. [All-root theorem and proof](linear-cutoffs.md)

For each $3\le k\le n$, the proposed theorem gives a simple negative closest nonzero root, strictly between the closest and all the remaining nonzero-root moduli in the next row. Reciprocation gives the largest root. In every sufficiently large row, all ranks through $\lfloor\tfrac14\sqrt{n/\log n}\rfloor$ at either end alternate, uniformly in the minimum cycle length $k$. [Statement and argument](proof.md) · [Alexandersson’s conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsPermutations) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)

**⬜ None.** The arguments are written. Exact integer checks of the extreme-root theorem cover 465 rows and 435 consecutive pairs through size 32. Reproduce the [archive](prefix.jsonl.gz) from the repository root using Python 3.10 or later.

~~~sh
python3 -I -O topics/long-cycle-excedances/verify.py
~~~

An independent agent-assisted review checked the run encoding, the explicit formula for the second coefficient, the root separation in consecutive rows, and the uniform binomial probability estimate. Real-rootedness for every row at fixed $k\ge3$ and consecutive interlacing of the interior roots remain open.
