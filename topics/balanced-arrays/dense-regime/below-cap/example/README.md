# Exact root comparison for seven rows, fourteen columns, and cap twelve

Consider the labeled binary arrays with $n=7$ rows, $d=14$ columns, and row cap $r=12$. In the capped polynomial $P$, coefficient $k$ counts arrays with each column sum equal to $k$. The unrestricted polynomial has coefficients $\binom{7}{k}^{14}$. The [complete coefficient vectors and certificates](example.json) give degrees six and seven, respectively. Each nonconstant capped coefficient differs from its unrestricted counterpart.

Let $c_j$ and $f_j$ be the positive magnitudes of the capped and unrestricted negative roots, in increasing order. Exactly the first three of the six comparisons by index satisfy $|c_j/f_j-1|<1/49$. The intervals below have exact rational endpoints.

| Index | Capped magnitude interval | Unrestricted magnitude interval | Within $1/49$ |
|---:|---|---|---|
| 1 | $(1.47445\times10^{-12},1.47446\times10^{-12})$ | $(1.47445\times10^{-12},1.47446\times10^{-12})$ | Yes |
| 2 | $(2.09129\times10^{-7},2.09131\times10^{-7})$ | $(2.09129\times10^{-7},2.09131\times10^{-7})$ | Yes |
| 3 | $(0.00078478,0.00078479)$ | $(0.00078404,0.00078405)$ | Yes |
| 4 | $(1.03154,1.03155)$ | $(0.99999,1.00001)$ | No |
| 5 | $(1980.73,1980.74)$ | $(1275.43,1275.44)$ | No |
| 6 | $(2969540000,2969550000)$ | $(4781726,4781727)$ | No |
| 7 | | $(678218289846,678218289847)$ | |

For each polynomial, the verifier checks opposite signs at the negated endpoints of every interval using rational Horner evaluation. The intervals are disjoint and their number equals the degree. This certifies one simple negative root per interval and accounts for all roots. For a matched pair of magnitude intervals $(L_c,U_c)$ and $(L_f,U_f)$, it checks that the ratio bounds $L_c/U_f$ and $U_c/L_f$ lie strictly between $1-1/49$ and $1+1/49$. For each remaining ordered pair it checks that both bounds lie outside on the same side.

The verifier reconstructs the capped coefficients by processing columns in order. For each row it records the number of zeros clipped at $d-r=2$. The column complement ranges over all labeled subsets of size $n-k$. After sorting the state, the edge multiplicity counts all complements giving that next state. Row permutation leaves each transition distribution the same, and the all-saturated terminal state enforces the cap. The result also agrees with the repository's remaining-capacity column recurrence and its existing [seven-row archive](https://github.com/ProgramComputer/open-math-research/blob/4e781edb3abd755443ac896561846b3888054fea/topics/balanced-arrays/results/column-extension-seven.jsonl.gz).

Run with the Python standard library from this directory.

~~~sh
python3 verify.py
archive_path=$(mktemp)
curl -fsSL https://raw.githubusercontent.com/ProgramComputer/open-math-research/4e781edb3abd755443ac896561846b3888054fea/topics/balanced-arrays/results/column-extension-seven.jsonl.gz -o "$archive_path"
python3 verify.py --archive "$archive_path"
~~~

The optional download checks the independent prior archive record. It ran in 0.04 seconds locally. This example illustrates finite root transfer and does not certify the asymptotic constants.
