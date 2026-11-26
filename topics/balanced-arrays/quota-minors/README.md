# Toeplitz minors in the balanced-array quota index

For labeled binary arrays with independent cell weights and the same allowed interval on each row in both copies, a coefficientwise balancing inequality gives nonnegative two-by-two minors of the factorial-normalized quota sequence. The smaller source margins must belong to the same copy across all columns. The inequality also gives nonnegative coefficients in the raw shifted Wronskian, which gives its sign on the positive axis. [Cellwise proof](cellwise-balancing.md) · [Independent order-two review](regular-toeplitz-order-two-review.md) · [Source comparison](cellwise-balancing-prior.md)

An inversion-sorting argument gives an explicit sufficient dimension condition for nonnegativity of each higher unnormalized straight minor. This statement is coefficientwise in the cell weights. For a common cap and unit weights it also gives a nonnegative expansion in the binomial basis of the variable row count. The matrix indices are quotas throughout. Arbitrary higher raw minors and the negative-axis interlacing question remain open. Factorial-normalized order-three positivity already fails at $`(n,r,d)=(9,1,2)`$, with a minor of determinant $`-1728`$. [Higher-minor proof and degree bound](quota-schur-minors.md) · [Independent higher-minor review](quota-schur-review.md) · [Order-three obstruction and small independent switch test](cellwise-switch-test/README.md)

**Formal verification.** ⬜ None.

## Exact computational evidence

For each listed pair $`(d,r)`$, the screen tests the unnormalized straight quota minors for every nonempty partition of weight at most $`L`$. Each determinant is a polynomial in the row count of degree at most $`d|\lambda|`$. Evaluations at $`0,\ldots,d|\lambda|`$ recover its exact binomial-basis coefficients. All coefficients in the 991 archived identities are nonnegative. The finite set of partitions gives evidence for the broader conjecture.

| $`(d,r,L)`$ | Partition polynomials | Archive |
| --- | ---: | --- |
| $`(4,2,14)`$ | 507 | [JSONL.gz](binomial-schur-4-2-14.jsonl.gz) |
| $`(5,3,11)`$ | 194 | [JSONL.gz](binomial-schur-5-3-11.jsonl.gz) |
| $`(5,2,11)`$ | 194 | [JSONL.gz](binomial-schur-5-2-11.jsonl.gz) |
| $`(6,3,9)`$ | 96 | [JSONL.gz](binomial-schur-6-3-9.jsonl.gz) |

With Python 3 and python-flint 0.9.0, run from this directory.

~~~sh
python3 -m pip install python-flint==0.9.0
python3 -I -B binomial-schur-screen.py 4 2 14
python3 -I -B binomial-schur-screen.py 5 3 11
python3 -I -B binomial-schur-screen.py 5 2 11
python3 -I -B binomial-schur-screen.py 6 3 9
~~~

Each command compares the reconstructed JSONL payload to the corresponding archive. Add --write to regenerate it. An independent standard-library check uses labeled-column tuples and inserts the permitted rows directly, then expands each selected determinant by permutations. It verifies 24 values at row counts 3 and 5 across the four profiles and the shapes $`(1,1,1)`$, $`(2,1)`$, and $`(3,1)`$.

~~~sh
python3 -I -B verify-direct.py
(cd cellwise-switch-test && python3 -I -B check.py | diff - manifest.jsonl)
~~~
