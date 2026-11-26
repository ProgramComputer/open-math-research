# A second sign certificate for all 508,000 roots

Take $`n=10^6`$, $`d=250000`$, $`r=127000`$. The reviewed result gives alternating geometric signs through quota 506,470 and from 507,905 onward. The following proof uses concentrated overlap of two independent arrays and the one-dimensional estimates from that earlier work. [Earlier signs and replays](../dense-regime/below-cap/finite-aspect/marked-row/README.md)

## Truncating the pairing estimate

Use the [marked-size comparison](likelihood.md). For each $`s<t`$, discard paired cell data in which some red-exclusive count $`h_j`$ exceeds $`K=260000`$. This event depends on the common and exclusive cell data alone. On the retained data the same proof gives the factor $`(1+1/K)^{t-s}`$. If at most an $`\epsilon`$ fraction of the source product is discarded, the full target is at least $`(1-\epsilon)(1+1/K)^{t-s}`$ times the full source. This is at least $`\lambda^{t-s}`$ for $`\lambda=(1-\epsilon)(1+1/K)`$.

The source is the product of the laws of two independent uniform arrays with margins $`\boldsymbol q`$ and $`\boldsymbol q+\mathbf1`$, specified marked sizes, and a specified missing column in the marked row. Condition further on their marked subsets separately. In either array the other $`N=n-1`$ rows are exchangeable. In column $`j`$ the red subset on these rows is uniform with a size $`x\le508000`$. The blue subset is independently uniform with size $`y\ge N/2`$ for every quota used in this note. Let $`H`$ count red entries outside the blue subset on these rows. For $`u>0`$, expanding over subsets of $`x`$ red positions gives

$$
\mathbb E(1+u)^H
=\sum_{m=0}^x\binom xm u^m\frac{(N-y)_{\underline m}}{N_{\underline m}}
\le \bigl(1+u(1-y/N)\bigr)^x .
$$

Here the underline denotes a falling factorial, with the numerator zero for $`m>N-y`$. Since $`h_j\le H+1`$, the discarded event in that column implies $`H\ge K`$. With $`u=1/25`$, Markov’s inequality and a union bound give

$$
\epsilon\le d(51/50)^{508000}(25/26)^{260000}<10^{-20}.
$$

The checker verifies this by grouping the powers into 1,000 identical blocks. The bound holds for all pairs of feasible marked subsets, hence for the source product after averaging. We may take $`\epsilon=10^{-20}`$ in the tilt and $`z=1-1/\lambda>1/260100`$.

## The mean deficit gives a curvature increment

At each base on the path from quota $`k-1`$ to $`k`$, the next column $`i`$ has the lower quota $`k-1`$. Write $`J`$ for the unrestricted marked size and $`U=r-J`$ for its deficit. At fixed size $`j`$, high-quota columns are at least as likely to be marked as low-quota columns. To see this, interchange a low mark with a high nonmark. In the residual array the two margins change from $`(k,k-2)`$ to $`(k-1,k-1)`$. Fix the other columns and the sum of the two cells in each row. Whenever the first fiber is nonempty the second has at least as many completions, because the binomial coefficient choosing half the singleton positions is maximal. Comparing the marked masks in pairs proves the assertion. Thus $`\Pr(X_i=0\mid J=j)\ge1-j/d`$. Row symmetry gives $`\Pr(X_i=0)=1-(k-1)/n`$. The functions $`r-J`$ and $`1-J/d`$ have nonnegative covariance, and $`\mathbb EJ\le dk/n`$. Consequently

$$
\mathbb E[U\mid X_i=0]\ge (r-dk/n)\frac{n-k}{n-k+1}.
$$

Write $`\mu`$ for this conditional mean. The conditional size probabilities are log-concave with interval support. Indeed, for two arrays of the same margins use the unweighted column pairings without dummy cells. At the marked vertex, with $`c`$ common cells, replacing the requirements $`(t-c,s-c)`$ by $`(t-1-c,s+1-c)`$ for $`t\ge s+2`$ satisfies Kahn and Neiman’s Lemma 8, just as in the marked-size comparison. All other rows have symmetric intervals in the two colors, and the forbidden mark in column $`i`$ is imposed in both. Thus the size weights satisfy $`F(t)F(s)\le F(t-1)F(s+1)`$. This proves both assertions.

In the missing-cell law put $`T_j=\Pr(U\ge j)`$. For a log-concave mass sequence with interval support the ratios $`T_{j+1}/T_j`$ decrease where defined. In fact $`T_j/\Pr(U=j)`$ decreases on the support, since each term $`\Pr(U=j+a)/\Pr(U=j)`$ is a product of decreasing consecutive mass ratios. Before the support the tail ratio is one. It follows from $`T_0=1`$ that $`T_{h+m}\le T_hT_m`$. For $`w=1-z\in(0,1)`$ and $`M=\sum_{h\ge1}T_hw^{h-1}`$ this gives

$$
\mu-M=z\sum_{h,m\ge1}w^{h-1}T_{h+m}\le z M\mu .
$$

Therefore $`\mathbb E w^U=1-zM\le1/(1+z\mu)`$. With $`e`$ and $`e^+`$ the original and increased saturation probabilities, the tilted comparison at the top size gives $`e^+\ge e/\mathbb E w^U\ge e(1+z\mu)`$. The increment in negative log survival is at least $`e^+-e`$. Orientation gives $`e\ge e(n,k-1)`$ at every phase. Telescoping as in the [general curvature argument](curvature.md) yields

$$
\log\frac{a_k^2}{a_{k-1}a_{k+1}}\ge
\frac{4d}{n+2}+\frac{d}{260100}e(n,k-1)(r-dk/n)\frac{n-k}{n-k+1}.
$$

## The exact sign replay

The program bounds $`e(n,k-1)`$ below by the published eighteen-step marked-row recursion or by the row-deficit theorem, taking the larger of the available bounds. For the latter, writing $`s=nr-d(k-1)`$ and $`R=r(d-r)/d`$, the lower bound is

$$
\frac{(d-r)n}{d(n-k+1)}\frac{n-1}{n+s-1}
\left(1-\min\left\lbrace
\frac{s(s-1)}{R n(n-1)}+\frac{s}{Rn}+\frac{2s}{rn},
\left(\frac2R+\frac2r\right)\frac{s(s-1)}{n(n-1)}
\right\rbrace\right).
$$

An upper bound on each required log curvature comes from consecutive mixed-phase brackets for the log decrement $`S_k`$ of the normalized cap probability. Add $`S_k^{\rm upper}-S_{k-1}^{\rm lower}`$ to $`d(1/k+1/(n-k))`$, an upper bound on the binomial log curvature. These brackets use the same published checker with additional rational tilt witnesses. [Mixed-phase bracket proof](../dense-regime/below-cap/finite-aspect/marked-row/mixed-phase/README.md) · [Row-deficit theorem](../dense-regime/below-cap/finite-aspect/upper-edge/paper.pdf)

At geometric center $`k`$, let $`a,b`$ bound below and above the five log curvatures at $`k-2,\ldots,k+2`$. The normalized magnitudes of offsets $`j`$ for $`|j|\le3`$ then lie between $`\exp(-bj^2/2)`$ and $`\exp(-aj^2/2)`$, by summing second differences with nonnegative weights totaling $`j^2/2`$. The checker verifies $`1-2\exp(-a/2)+2\exp(-2b)-2\exp(-9a/2)>0`$ at the centers where it uses these brackets. The remaining alternating terms starting at distance four pair nonnegatively. At the other centers a log curvature exceeding $`\log4`$ suffices. All integer indices in the gap are covered. The signs at zero, the strictly ordered geometric radii and negative infinity supply all the distinct roots, as in the general criterion. [Exact checker](verify-finite.py)
