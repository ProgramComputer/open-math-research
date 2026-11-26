# Simple negative roots at one million rows

**Finite theorem.** For $`n=1000000`$ labeled rows, $`d=250000`$ labeled columns and row cap $`r=127000`$, the balanced-array polynomial has exactly 508,000 simple negative roots. The conjecture quantifies over every admissible triple. [Original statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

Write $`a_k`$ for the number of arrays with common column sum $`k`$. Its support runs from zero to $`D=nr/d=508000`$. For each feasible $`k`$, distribute $`dk`$ successive positions around a cyclic list of the rows, allocating each successive block of $`k`$ positions to one column. Each column uses distinct rows and the maximum row sum is at most $`r`$.

For $`0<k<D`$ put $`v_k=\sqrt{a_{k-1}/a_{k+1}}`$. The following arguments give $`(-1)^kP(-v_k)>0`$ on adjoining integer intervals.

| Geometric indices, inclusive | Argument |
| --- | --- |
| 1 through 505,661 | [Interior and marked-row bounds](../paper.pdf) |
| 505,662 through 506,470 | [Mixed-phase bounds and independent replay](../mixed-phase/README.md) |
| 506,471 through 507,300 | [Recursion centered at the truncated binomial law with the same mean](centered.md) |
| 507,300 through 507,905 | [Row-switching estimate and comparison of consecutive row sizes](phase-order.md) |
| 507,905 through 507,999 | [Outer row-deficit bound](../../upper-edge/paper.pdf) |

The global strict log-concavity orders the $`v_k`$ strictly. The constant term is one and the sign at sufficiently large negative argument is $`(-1)^D`$. The intermediate value theorem gives one negative real root in each of the $`D`$ disjoint open intervals cut out by the test points. The degree forces each root to have multiplicity one. The two overlaps in the table provide a check on the joins. [Global coefficient bound](../../../../../orientation-normalization.md)

**Formal verification**　⬜ None. An independent mathematical review checked the two middle arguments, replayed their rational checks and verified coverage of all 507,999 internal indices. [Independent review](review.md) · [Earlier reviewed finite result](https://github.com/ProgramComputer/open-math-research/pull/183)

From this directory run the following command with Python 3 and its standard library. It executes the component checkers in fresh processes, compares both new outputs against the recorded values and checks that the intervals cover every internal index. The calculations bound signs directly from the array model.

~~~sh
python3 -IB verify.py
python3 -IB phase-order-independent.py
~~~

[Research log and literature screen](research-log.md)
