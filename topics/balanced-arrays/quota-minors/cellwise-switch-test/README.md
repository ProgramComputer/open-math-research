# Independent small test of cellwise balancing

Signed by agent-assisted reviewer four_blind, 2026-11-26.

**Verdict.** The coefficientwise comparison and the raw Wronskian coefficient sign check out. The finite checks found no violation. The tests cover five explicitly listed profiles on at most four rows and four columns. They include unequal source margin vectors, heterogeneous intervals common to the two copies, compulsory nonempty rows, two exact-size rows in one profile, a compulsory empty row, a transfer equal to the full column gap, and zero transfer coordinates.

## Replay and exact comparisons

Run from this directory using the Python standard library.

~~~sh
python3 -B check.py | diff - manifest.jsonl
~~~

The [checker](check.py) enumerates all permitted sequences of labeled row masks, indexes the actual arrays by margin vector, and enumerates pairs at the two source and two target margins. The coefficient bucket key records, by column, a common-cell mask and an exclusive-cell mask. The checker verifies both the exact local-factor inequality and the comparison of its local multiplier with the global multiplier by integer cross multiplication. It also specializes the independent cell variables using four maps, keeping them distinct, merging by rows, merging by columns and merging via a mixed cell-dependent map. Each resulting polynomial comparison is checked again by integer cross multiplication.

The checker separately constructs all compatible red-blue pairings of the augmented masks, dropping any dummy-dummy pairs. It records labeled undirected edge lists and compares source and target counts for each source-refined skeleton. The factorial formulas for total source and target refinement multiplicities are also checked against these independent sums. The [manifest](manifest.jsonl) gives exact per-case counts.

## Mathematical audit

At a real row let $`C`$ be the number of common cells and $`E`$ the number of exclusive cells. Under an orientation the occupancies there are $`C+\mathrm{outdeg}`$ and $`C+\mathrm{indeg}`$. Since $`\mathrm{outdeg}+\mathrm{indeg}=E`$, the two intervals are equivalent to the same lower bound $`\max(0,L-C,E+C-U)`$ in each direction. The source has bounds $`(1,0)`$ at each dummy (outdegree first), and the target either retains these or flips to $`(0,1)`$. Thus source first bounds dominate both target bounds at each vertex, and pointwise sums agree. These are the hypotheses of the graph-orientation inequality. Real pairs from different columns may give parallel edges, whose column labels are retained. [Kahn–Neiman, §4, Lemma 8](https://arxiv.org/pdf/1001.0610)

For the raw Wronskian $`F'_{\mathbf u}F_{\mathbf u+\mathbf e_i}-F_{\mathbf u}F'_{\mathbf u+\mathbf e_i}`$, pairing the $`(k,l)`$ and $`(l,k)`$ terms gives the difference stated in the proof with factor $`k-l`$ and exponent $`k+l-1`$. For $`k>l`$, the two margins of the subtracted product are $`\mathbf a=l\mathbf1+\mathbf u`$ and $`\mathbf b=k\mathbf1+\mathbf u+\mathbf e_i`$. A one-unit transfer only in coordinate $`i`$ gives the two margins in the positive product. Its unshifted exclusive-factor ratio is at least one, since $`b_i-a_i=k-l+1\ge2`$. This proves nonnegative coefficients before any evaluation. The checker also forms the Wronskian directly as a signed sum of pair buckets, for the zero offset and a mixed-sign offset, testing all coordinate directions. Nonnegative coefficients imply the sign on the positive axis only. The negative-axis sign needed for directed interlacing remains open.

The raw higher-order coefficientwise and binomial-basis routes are open here. The direct extension of the factorial normalization to third-order Toeplitz minors fails already at $`n=9,d=2,r=1`$. With cap one and two columns, the normalized sequence is $`b_k=(k!)^2a_k=9!/(9-2k)!`$ for $`0\le k\le4`$. For the Toeplitz matrix with entry $`b_{j-i}`$ and zero outside support, rows $`(0,1,2)`$ and columns $`(1,2,3)`$ give

$$
\det\begin{pmatrix}
72&3024&60480\\
1&72&3024\\
0&1&72
\end{pmatrix}=-1728.
$$

This distinguishes the failed factorial-normalized strengthening from the raw unweighted question.
