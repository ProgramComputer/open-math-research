# Five residual balanced-array cases at 36 rows

For [Per Alexandersson’s balanced-array conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) eight cases at 36 rows were pending after an earlier partial replay and a separate corank-two count. This package certifies five of those eight, each with as many distinct negative roots as its degree. [Finite reduction and earlier coverage](../finite-residual/README.md)

| Rows | Cap | Columns | Simple negative roots |
| ---: | ---: | ---: | ---: |
| 36 | 7 | 11 | 22 |
| 36 | 8 | 11 | 26 |
| 36 | 8 | 12 | 24 |
| 36 | 9 | 12 | 27 |
| 36 | 10 | 12 | 30 |

Three residual cases are outside this package. They have 12 columns and caps five, six and seven.

## Exact proofs and replay

The [defect histogram](defect-histogram.md) counts each coefficient by inclusion–exclusion on overloaded labeled rows. Its five output files give complete exact vectors. The shared rational Sturm replay establishes the full negative root count for each vector. Direct enumeration also checks the counting recurrence and its truncated bounds at 280 small inputs. In three of these five cases, separate counters using simpler recurrences independently give exact rational sign certificates.

For cap ten and 12 columns there are also two proofs using row failure probability bounds. The first proves alternating signs at geometric nodes by retaining the second term on each side and controlling the third by log-concavity. The second uses four joint row-failure moments and nine explicit rational sign probes, with exact comparisons at the two joins to the outer nodes. Both use the [validity-probability log-concavity theorem](../orientation-normalization.md). [Geometric compensation proof and independent review](independent-review.md)

Run these standard-library commands from this directory.

~~~sh
python3 -B compensation.py
python3 -B independent-probes.py
python3 -B independent-count.py
python3 -B independent-near-full.py
python3 -B defect-check.py
~~~

The complete five-vector Sturm replay additionally needs `python-flint==0.9.0`.

~~~sh
python3 -B defect-check.py --shared ../../../shared/python defect-d*.jsonl
~~~

**Formal verification**　⬜ None. The recurrence, inequalities and implementation received agent-assisted checks.
