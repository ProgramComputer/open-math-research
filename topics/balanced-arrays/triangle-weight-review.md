# Independent review of the weighted triangle obstruction

For labeled rows of size at most two, I independently enumerated each column's occupied $k$-subset of the rows. I rejected assignments with a row larger than two and counted the surviving arrays by the number of rows equal to $12$, $13$, or $23$. Those row types have weight $t$, and every other allowed row type has weight one. Since $4k\le 2n$, the enumeration exhausts all coefficients when $n=4,5$.

```python
from collections import Counter
from itertools import combinations, product

heavy = {(1, 2), (1, 3), (2, 3)}
for n in (4, 5):
    for k in range(n // 2 + 1):
        counts = Counter()
        for cols in product(list(combinations(range(n), k)), repeat=4):
            rows = [tuple(j + 1 for j, col in enumerate(cols) if i in col)
                    for i in range(n)]
            if all(len(row) <= 2 for row in rows):
                counts[sum(row in heavy for row in rows)] += 1
        print(n, k, sorted(counts.items()))
```

At $n=5$ this gives
$$
1+(300+240t)q+(1080t+1350t^2+60t^3)q^2.
$$
At $t=256$ the coefficients are $(1,61740,1095383040)$ and the exact discriminant is $-569704560$. At $n=4$ the polynomial is $1+(96+108t)q+90t^2q^2$, with discriminant $9216+20736t+11304t^2>0$ for $t\ge0$. The rows $n<4$ have degree at most one.

## General matching obstruction

Let $c_{ij}\ge0$ be the exponent on the weight $t^{c_{ij}}$ for the two-column row $ij$. Empty rows and singletons have weight one. Let $\nu$ be the maximum exponent sum of an ordinary matching and $\nu^*$ the maximum of $\sum_{ij}c_{ij}x_{ij}$ over nonnegative $x$ with incident sums at most one.

In a quota-one array the paired columns are an ordinary matching, since each column occurs just once. Each array contributes at most $t^\nu$ for $t\ge1$ and there are at most $n^d$ arrays. For quota two, choose an optimal half-integral fractional matching $x$ and assign $2x_{ij}$ distinct rows to pair $ij$. Give each column $i$ an additional $2-\sum_j2x_{ij}$ singleton rows. The number of nonempty rows is $2d-\sum_{ij}2x_{ij}\le 2d$. Once this fits in $n$ rows, fill any remaining rows with empties. This yields $a_2\ge t^{2\nu^*}$. The half-integrality used here is classical. The paired-row construction is the weighted form of the occurrence-matching interpretation in the original issue. [Balinski (1965)](https://doi.org/10.1287/MNSC.12.3.253) · [Alexandersson, issue #2005](https://github.com/PerAlexandersson/RealRooted/issues/2005)

Consequently $a_1^2/a_2\le n^{2d}t^{-2(\nu^*-\nu)}\to0$ for fixed $n$ if $\nu^*>\nu$. Real-rootedness with nonnegative coefficients and $a_0=1$ implies $a_1^2\ge2a_2$, since writing $P(q)=\prod_j(1+\lambda_jq)$ with $\lambda_j>0$ gives $a_1^2=2a_2+\sum_j\lambda_j^2$. Thus for each fixed $n$ meeting the row bound the weighted polynomial has a nonreal zero at all sufficiently large $t$. The threshold can depend on $n$.

For the four-column triangle $\nu=1$ and $\nu^*=3/2$. Summing the three incident constraints bounds the total on the heavy edges by $3/2$, attained by weighting those edges by $1/2$ each. The doubled solution uses three triangle pair rows and two singleton rows in column 4, so it fits at every $n\ge5$. At least $(n)_5/2$ labelings give the $t^3$ term. The degree-one upper bound is $a_1\le n^4t$, so $t>2n^8/(n)_5$ already forces $a_1^2<a_2$.

## Consequence and attribution

A Hermite matrix for the six independent nonnegative pair weights cannot have every coefficient matrix positive semidefinite, since that would make every positive specialization positive semidefinite and imply real-rootedness by the Hermite criterion. The triangle gives a strictly positive specialization with a negative discriminant. The same obstruction applies to any coefficientwise certificate of that kind whose positive specializations would suffice to prove real-rootedness. A statement restricted to all six weights equal to one, or to another parameter subfamily, is outside this obstruction.

On 2026-11-25, I searched public web indexes with `"balanced arrays" real-rooted weighted triangle`, `"equal column sums" "diagonal" real-rooted weighted binary matrices polynomial counterexample`, and variants containing `"fractional matching"`, `Alexandersson`, and the GitHub and X domains. The direct related source found was Alexandersson's unweighted matching expansion in issue #2005. The repository also records a failure for row-size-dependent weights at different parameters in an earlier project note. I found no direct predecessor for this triangle specialization or the fractional-optimum criterion. The X check used public search-engine indexing, which can omit posts. This is a scoped search finding rather than a priority claim.
