# Direct weighted balanced-array checks

Agent-assisted independent computation by Codex. No counterexample appeared in the stated finite ranges. This is an exhaustive check of one small family and a seeded sample of larger families.

Run from this directory using Python 3.10 or later and the standard library.

~~~sh
python3 check.py
~~~

The script enumerates labeled binary arrays as tuples of column subsets. It imposes separate inclusive lower and upper bounds on every row. The weight of an array is the product of the weights of its occupied cells. It accumulates weighted counts by column margins and also by the marked column's complete Boolean mask with the remaining margins fixed. All sums and comparisons use Python integers.

## Tested models

The exhaustive family has two rows and three columns. It contains all 64 zero-one cell-weight patterns and all 100 tuples of two intervals in the range 0 to 3, for 6,400 models. The other 1,005 models have heterogeneous weights sampled independently from the multiset (0, 1, 1, 2, 3, 7), with independently sampled row intervals. The fixed seed is 20261126. There are 250 sampled 2-by-3, 500 sampled 3-by-3, 225 sampled 4-by-3, and 30 sampled 4-by-4 models.

## Results

| Check | Comparisons |
| --- | ---: |
| One-column binomially normalized log-concavity | 323,175 |
| Off-diagonal mixed adjacent inequality | 419,400 |
| Binomially normalized diagonal log-concavity | 8,415 |
| Support inside boxes between comparable feasible vectors | 1,475,015 |
| Conditional antipodal pairs property (CAPP) | 244,381 |

These figures cover 7,405 models and 3,569,280 possible binary arrays, counted across models. The enumeration skips zero-weight column masks and retains 131,601 positive-weight arrays that satisfy the row intervals. The inequality totals include zero cases. The support total counts the tested interior points of comparable endpoint boxes with repetitions across boxes. CAPP counts positive conditioning events.

For the one-column and diagonal checks, the script multiplies by the positive binomial denominators before comparing. The mixed comparison cancels those denominators. For CAPP, it considers each even free subset of at least two row labels and each positive-mass assignment outside it. At each of the middle and preceding ranks it sums the products of the unnormalized masses of opposite free masks. It compares the two averages after multiplying by their binomial denominators. The common conditional normalizer cancels.

The script prints the first witness per failed category and returns a nonzero status if any category fails. The [recorded output](output.txt) shows that all five categories passed.

The compressed [model ledger](models.jsonl.gz) records all row intervals and cell weights, every positive quota profile and its weight, the full common-quota coefficient vector (including zero coefficients), the comparison count for each method and any failures. Missing profiles have weight zero. The standard-library commands below reproduce the ledger and check the separate four-row counterexample.

~~~sh
python3 -IB check.py --ledger /tmp/balanced-weighted-models.jsonl.gz
gzip -dc /tmp/balanced-weighted-models.jsonl.gz | cmp - <(gzip -dc models.jsonl.gz)
python3 -IB check-marginal.py
python3 -IB check-marked-odds.py
~~~

The comparison command uses Bash process substitution. The [marked-row probe](check-marked-odds.py) uses a fixed seed and directly enumerates weighted row fibers for its homogeneous margins. Its [output](marked-checks.txt) is finite evidence for the reported models.
