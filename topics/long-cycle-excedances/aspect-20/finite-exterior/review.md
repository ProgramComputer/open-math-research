# Independent check of the finite exterior roots

On November 26, 2026, an independent agent-assisted review reconstructed all 114,750 pairs with $251\le n\le1000$ and $4\le k\le n/4$. An independently written checker verified 991,894 one-sided old ranks, the actual next-row signs and the common-circle entrance in every pair. Formal coverage is ⬜ None.

Write $P_n=E_{n,k}/t$, $c_j=[t^j]P_n$, and $c_j^{\prime}$ for the next reduced row. The checker separately generates the one-cycle coefficients by Eulerian finite differences. The deletion/insertion recurrence gives $c_j^{\prime}=(j+1)c_j+(n-j)c_{j-1}$ plus the coefficient of the distinguished cycle times the residual row. At threshold $k$ the initial row is the single-cycle row. The checker keeps the last $k$ prefixes in a ring, computing the distinguished residual from size $n+1-k$ before overwriting its slot. Truncation preserves every computed low coefficient because all polynomial exponents are nonnegative.

At rank $h$, with the exact old and new adjacent coefficient scales $u,v$, my replay uses $u\pm2(u-v)/5$. At each endpoint I checked strict dominant-monomial inequalities in both polynomials. The checker uses six central indices and separate geometric bounds for both omitted tails, derived from $[t^p]E_{n,k}\le p^n$. The series ratios decrease as one moves away from the central indices. A missing left tail has zero cost. The arithmetic keeps rigorous balls around the positive quantities and their differences.

By Rouché, the old disks have zero counts $h,h+1$ including the common zero. At those same radii the new disks both have count $h+1$. The old signs at the two endpoints are opposite, so the annular zero is simple and negative, and the next row's sign there equals the sign at the inner endpoint. The old root interval for each rank precedes the common-circle entrance at the final tested rank. The direct next-row sign and old-root count suffice for the join. These finite checks establish exterior roots only.

Run the [independent checker](review_front.py) with python-flint 0.9.0 using `python -I -B review_front.py`. Its [recorded output](review-output.txt) reports the completed pair and rank counts.
