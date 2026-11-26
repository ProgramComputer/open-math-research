# Exact inclusion–exclusion using overloaded-row defect histograms

At $`n=36`$ this gives independent coefficient counts for the previously unrecounted cases with corank two, three, and four. The implementation needs only Python's standard library. It counts arrays directly by exact inclusion–exclusion over subsets of overloaded labeled rows. It does not read prior coefficient archives.

Let $`J_h`$ count arrays of common column quota $`k`$ in which a prescribed set of $`h`$ rows all have occupancy at least $`r+1`$. Then

$$
a(n,k,r,d)=\sum_{h=0}^{\min(n,\lfloor dk/(r+1)\rfloor)}(-1)^h\binom nh J_h,
\qquad J_0=\binom nk^d.
$$

The endpoint uses the deterministic total of $`dk`$ ones. Early termination at $`J_h=0`$ is exact because the event defining later joint tails is contained in an event prescribing just $`h`$ of its rows. At any earlier stopping point, alternating even and odd partial sums bound the coefficient by Bonferroni.

Each prescribed overloaded row has at most $`c=d-r-1`$ missing cells. After processing a prefix of columns, let $`H_i`$ be the number of specified rows with exactly $`i`$ misses for $`0\le i\le c`$. Initially $`H_0=h`$. For the next column choose $`b_i`$ misses from the $`i`$-group, where $`0\le b_i\le H_i`$ for $`i<c`$, and $`b_c=0`$. If $`B=\sum_i b_i`$, the prescribed rows occupy $`h-B`$ cells in this column, so transitions have weight

$$
\binom{n-h}{k-h+B}\prod_{i<c}\binom{H_i}{b_i}.
$$

Update by moving the $`b_i`$ rows from group $`i`$ to group $`i+1`$, treating all moves simultaneously. A DP value is the number of labeled partial arrays realizing the histogram. The transitions count choices of labeled rows within every group, so aggregation preserves multiplicities. At the end sum all DP values. Intermediate pruning uses the total remaining miss budget of the specified rows, since each further column must miss at least $`\max(0,h-k)`$ of them. The histogram has at most $`\binom{h+c}{c}`$ states.

## Replay

Run `python3 defect-histogram.py 36 12 10` to emit coefficients with exact lower and upper integer bounds for every quota. Use `--min-k`, `--max-k`, or `--order` to restrict quotas or stop inclusion–exclusion at an early order. The current JSONL files include measured per-quota runtimes and are otherwise complete exact count records wherever their quota ranges are complete.

Run `python3 -B defect-check.py` to check exact counts and truncations through order three against brute force over independent column choices for all $`1\le n\le5`$, $`1\le d\le4`$, every cap $`0\le r\le d`$, and every quota $`0\le k\le n`$. This passed all 280 combinations. For root checks, run `defect-check.py --shared PATH/TO/shared/python defect-d12-r10.jsonl` with the project's Python environment, which supplies python-flint. It uses the project's primitive rational Sturm checker.

## Completed row-36 counts

Every listed vector is complete and has strictly positive coefficients. The primitive rational Sturm replay returned the full degree as the number of distinct negative roots, with right variation zero.

| Columns | Cap | Degree | Count time in seconds |
| ---: | ---: | ---: | ---: |
| 11 | 7 | 22 | 99.992 |
| 11 | 8 | 26 | 7.600 |
| 12 | 8 | 24 | 162.518 |
| 12 | 9 | 27 | 9.113 |
| 12 | 10 | 30 | 0.258 |

The three remaining cases at 36 rows have 12 columns and caps five, six and seven.
