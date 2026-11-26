# Log-concavity failures under hereditary row restrictions

A hereditary row family specifies the allowed supports of a binary row and is closed under taking subsets. The [strong Koszul and ribbon positivity theorems](../README.md) allow arbitrary hereditary families. The following examples show that balanced-quota log-concavity can fail in that setting, even with the same family in every row and all cell weights one. Alexandersson's conjecture uses uniform cardinality caps and remains open in general. [Original problem](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays).

Write $`a_k`$ for the count at common quota $`k`$. Each example exhibits a strict reversal of $`a_k^2\ge a_{k-1}a_{k+1}`$. A polynomial with nonnegative coefficients and constant term one that is real-rooted has all roots negative and satisfies this inequality.

## Six columns and identical row supports

Split the columns into two blocks of three. A row may contain any subset of the first block or any subset of size at most two from the second block. Take $`n=5t`$ and let $`A_j=a_{2t-j}`$. The [proof and signed check](identical-review.md) give

$$
\frac{A_1^2}{A_0A_2}\sim\frac{60750}{t}.
$$

In particular the quota sequence fails log-concavity for all sufficiently large integers $`t`$. The exact witness at $`t=100000`$ has ratio below $`61/100`$.

## Nine columns and identical pure flag row supports

Use the clique complex of the disjoint union of a triangle and a wheel with five rim vertices, on nine columns. Every maximal allowed support is a triangle. For $`n=7t`$, the [proof and signed check](flag-review.md) give

$$
\frac{a_{2t-2}a_{2t}}{a_{2t-1}^2}=\Theta(t).
$$

Thus purity and the flag condition still allow log-concavity to fail with identical row families and unit weights. The [exact finite replay](flag-manifest.txt) certifies a witness at $`700{,}000{,}000`$ rows and checks a separate seven-row instance by direct enumeration.

## Weighted illustration

On a four-by-four array, let row $`i`$ allow its diagonal singleton and every subset of the other three cells. Give diagonal cells weight 20 and other cells weight one. Direct enumeration gives the ascending coefficient vector $`(1,163121,321,1)`$, with $`321^2-163121=-60080`$.

## Reproduction

Run from this directory with Python 3. The exact checkers use only the standard library.

```sh
python3 -B check-identical.py | diff - identical-manifest.txt
python3 -B check-flag.py | diff - flag-manifest.txt
python3 -B check-witness.py
```

**Verification.** The asymptotic arguments received independent agent-assisted mathematical reviews. No Lean or Rocq proof is claimed.
