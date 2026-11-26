# Where the roots of balanced arrays lie

Let $`P(q)`$ count labeled $`n\times d`$ binary arrays by their common column sum, with every row sum at most $`r`$. Write $`\xi`$ for a complex zero of $`P`$, counted with multiplicity, and let $`C(t)`$ count such zeros of modulus at most $`t`$. If $`n,d\to\infty`$ and $`r/d\to\rho>0`$, then for every $`z>0`$,

$$
\frac{C(z^d)}{n}
\longrightarrow \min\left(\frac{z}{1+z},\rho\right).
$$

There is no restriction on the relative growth of height and dimension. Theorem 4 of the manuscript gives an explicit error bound at finite height and dimension. These results describe root moduli. Whether all zeros are real for every finite triple remains open. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Manuscript](paper.pdf) · [LaTeX source](paper.tex)

Four additional limits describe what happens near small caps and near full caps. In each row the limit is the number of roots with the stated scaled modulus at most $`z`$, divided by the indicated normalization. Here $`X_z`$ is Poisson with mean $`z`$.

| Row cap or corank | Scaled modulus | Normalization | Limiting count |
|---|---|---|---|
| Fixed cap $`r=b`$, $`d=o(n)`$ | $`d\,\lvert\xi\rvert^{1/d}`$ | $`n/d`$ | $`\mathbb E[X_z\mid X_z\le b]`$ |
| Fixed corank $`d-r=h\ge1`$, $`d=o(n)`$ | $`d/\lvert\xi\rvert^{1/d}`$ | $`n/d`$ | $`\mathbb E[X_z\mid X_z\ge h]-h`$ |
| Growing cap $`r=s=o(d)`$ | $`(d/s)\lvert\xi\rvert^{1/d}`$ | $`ns/d`$ | $`\min(z,1)`$ |
| Growing corank $`d-r=s=o(d)`$ | $`(d/s)/\lvert\xi\rvert^{1/d}`$ | $`ns/d`$ | $`\max(z-1,0)`$ |

Both growing cases assume $`s\to\infty`$ and $`ns/d\to\infty`$. In the growing-cap case the entire empirical distribution converges to the **uniform law on the unit interval**. In the two corank cases the count describes the largest original roots. Reciprocating the polynomial introduces zero roots, which must be removed from that count.

**Formal verification**　⬜ None. An independent agent reviewed the five limits and the finite estimate from the array definition. [Mathematical review](review.md) · [Sources and status](literature.md)

At one million rows, 250,000 columns and cap 127,000, the finite theorem places between 324,834 and 341,833 roots within radius $`2^{-250000}`$. At 64 rows and columns with cap 63, an independent integer calculation gives exactly 32 roots in the unit disk. [Exact checks and reproduction](verification/README.md)
