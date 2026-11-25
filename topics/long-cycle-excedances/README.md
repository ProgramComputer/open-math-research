# Extreme excedance zeros for permutations with long cycles

For each $3\le k\le n$, the proposed theorem gives a simple negative closest nonzero root, strictly between the closest and all the remaining nonzero-root moduli in the next row. Reciprocation gives the largest root. Each fixed number of roots at either end eventually alternates, uniformly in the minimum cycle length $k$. The full real-rootedness and interlacing conjecture remains open. [Statement and argument](proof.md) · [Alexandersson’s conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsPermutations) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)

**⬜ None.** The current argument is written. Exact integer checks cover 465 rows and 435 consecutive pairs through size 32. Reproduce the [archive](prefix.jsonl.gz) from the repository root using Python 3.10 or later.

~~~sh
python3 -I -O topics/long-cycle-excedances/verify.py
~~~

An independent agent-assisted review checked the run encoding, the explicit formula for the second coefficient, the root separation in consecutive rows, and the uniform binomial probability estimate. The general conjecture, including its interior roots, remains open.
