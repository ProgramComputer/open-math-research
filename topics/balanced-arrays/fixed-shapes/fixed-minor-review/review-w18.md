# Independent replay of the weight-18 straight-shape certificates

Signed by agent-assisted reviewer four_blind, 2026-11-26.

**Verdict.** All 1,596 cutoff records and all 5,581 residual polynomial identities agree with the independent replay. Every residual binomial-basis coefficient is nonnegative. I found no missing or duplicate shape or residual key. The scope is straight shapes of positive weight at most 18. It does not include an unrestricted claim about skew shapes, higher weights, or real-rootedness of every original array polynomial.

## Cutoffs and coverage

I generated the partitions of each weight from 1 to 18 and verified exact set coverage. There are 99 shapes of length at most two, 136 hooks of larger length, and 1,361 shapes handled by an exact factorial threshold. The number of latter shapes at thresholds 1 through 6 is 95, 291, 427, 384, 151 and 13, respectively. The order-two and hook classifications use the existing reviewed order-two and ribbon arguments. This replay checks their applicability by shape.

For each threshold record with fixed partition $`\lambda`$, I used a subset recursion keeping separate sums for even and odd partial assignments. For row $`i`$ and column $`j`$, write $`q=\lambda_i-i+j`$ and $`u=\lambda_i-i+\ell-1`$, where $`\ell`$ is the partition length and both indices are zero-based. The integral table entry is $`(u!/q!)^d`$ when $`q\ge0`$, and zero otherwise. Adding a column bit $`j`$ toggles parity according to the number of already selected bits strictly above $`j`$. The odd sum at completion is compared to the product of the diagonal entries. This cancels the common row scale and exactly tests the factorial domination bound. Every reported threshold passes, and the previous positive dimension fails when present. Strict contraction in each sorted nonidentity term gives monotonicity in dimension, as in the [earlier independent review](README.md). The missing dimensions and their caps determine the residual keys independently of the residual archive.

## Residual polynomials

I reconstructed the counts by adding whole labeled columns. The state is a histogram of current row loads, and one column selects the required quota from bins strictly below the cap. Selections with a specified count in each bin have multiplicity equal to a product of ordinary binomial coefficients. I used direct formulas for cap one, full rank and corank one. The last is inclusion–exclusion on fully occupied rows. As an independent spot check of these counting routines, unsorted labeled row-by-row enumeration exactly matched 225 counts through four rows and five columns.

For each needed shape, dimension and cap, I evaluated the determinant for every integer height from zero to $`d|\lambda|`$. I used dual Jacobi–Trudi on the conjugate partition. The elementary series was computed coefficientwise as $`E(t)=1/H(-t)`$, where $`H`$ is the balanced quota series at that height. The resulting integer determinant was computed in FLINT. A separate signed permutation expansion matched 4,152 determinant evaluations for shapes of length at most five. Forward differences at zero gave the full binomial-basis vector. The degree bound $`d|\lambda|`$ follows by classifying product terms by which row labels appear across the factors, so these comparisons verify entire polynomial identities.

The checked residual dimensions 1 through 5 contain, respectively, 1,266, 1,950, 1,644, 656 and 65 records. The canonical digest below uses compact JSON arrays containing shape, dimension, cap and the computed coefficient vector, one newline-terminated record per archive line.

| Artifact | SHA-256 |
| --- | --- |
| Cutoff archive | 2c728248ea57bd8c181684b8886a1b56e80260624fbcfa5db19d520f3467952e |
| Compressed residual archive | 6949f12ea6f44af104a91f6b73642264a4fa10994fee8fd8bb11ae305fce8f8b |
| Canonical independently replayed residual vectors | b2abe93e21960f134fa08ef1b43aaca68c4bde669867267bc8cdf226c71c36b7 |

Run the [independent script](replay_w18.py) with Python and python-flint. It reads the existing sibling archive files, checks the full content and prints the hashes. The [replay log](replay_w18.log) records one successful run.
