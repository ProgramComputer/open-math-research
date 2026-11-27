# Bracketing the old largest root at the degree carry

Let $`O_{n,j}`$ count all ordered partitions by the number of blocks of size at least $`j`$. Let $`n=j(m+1)-1`$, so the old and next degrees are $`m`$ and $`m+1`$. Suppose $`m\to\infty`$ and $`j/m^2\to\infty`$. Then the old largest-modulus zero and both largest-modulus next zeros are simple and negative. Writing moduli in descending order, they satisfy

$$
 Q_{n+1,1}>Q_{n,1}>Q_{n+1,2},
 \qquad \frac{Q_{n,1}-Q_{n+1,2}}{Q_{n,1}}\sim \frac{m}{2j}.
$$

This extends the one-root carry estimate in the [joint coefficient note](large-excess.md). It brackets the actual old root by both final new roots, even when the relative gap between the old root and the nearer new root is exponentially small in $`m`$.

Use $`a_p(e)=[z^e]T_j(\rho z)^{p+1}L_j(\rho z)^p`$ and $`D=j!\rho^{-j}`$, in the notation of the [coefficient note](large-excess.md). Let $`b_h^-`$ and $`b_h^+`$ be the reversed coefficients normalized by their own leading coefficients. Positivity and the reciprocal EGF give the exact identities

$$
 b_h^-=D^h\frac{a_{m-h}(j(h+1)-1)}{a_m(j-1)},\qquad
 b_{h+1}^+=D^{h+1}a_{m-h}(j(h+1)),\qquad 0\le h\le m .
$$

In particular $`b_1^+=Da_m(j)`$. Define

$$
 \gamma_h=\frac{a_{m-h}(j(h+1))}{a_{m-h}(j(h+1)-1)},\quad
 B=\frac{b_1^+}{b_1^-},\quad
 \beta_h=\frac{b_h^-}{(b_1^-)^h},\quad
 \alpha_h=\frac{\gamma_h}{\gamma_0}.
$$

There is exact cancellation of all factorial and normalization factors in

$$
 \frac{b_{h+1}^+}{b_1^+}=b_h^-\alpha_h .
$$

This compares the deflated next row with the old row at adjacent excess indices.

With the old scaling $`x=b_1^-/t`$, let $`R^-(x)`$ and $`R^+(x)`$ be the reversed rows with constant term one. Then

$$
 R^-(x)=1+x+\sum_{h\ge2}\beta_h x^h,\qquad
 \frac{R^+(x)}B=\frac1B+x\left(1+\alpha_1 x+\sum_{h\ge2}\alpha_h\beta_h x^h\right).
$$

From the uniform coefficient and increment estimates in the [coefficient note](large-excess.md), one has

$$
 \sum_{h\ge2}\beta_h 2^h=o(1),\quad
 \alpha_1-1\sim-\frac m{2j},\quad
 \max_{0\le h\le m}|\alpha_h-1|=O(m/j).
$$

Indeed $`\gamma_0=1+(1+o(1))m/j`$, and $`\gamma_1=1+(1+o(1))(m-1)/(2j)`$. At $`h=m`$, the direct estimate for $`a_0`$ gives $`\gamma_m-1=o(m/j)`$. The coefficient lemma also gives

$$
 B\sim\frac{c^{m+2} j^{m+1}}{m!\thinspace m\thinspace 2^{m-1}},
 \qquad B^{-1}=o(m/j).
$$

For the last bound use $`m!\le m^m`$ and $`j/m\to\infty`$.

On $`|x|=2`$, the old comparison is $`1+x`$, and the next comparison after division by $`B`$ is $`x(1+x)`$. Rouché counts one and two zeros, respectively, in these disks. Smaller disjoint disks about $`0`$ and $`-1`$ isolate the next zeros individually by the same argument. The old zero tends to $`-1`$, and the next zeros tend to $`0`$ and $`-1`$. Conjugation gives reality and simplicity; positivity of the real coefficients gives negativity. Thus these are precisely the reciprocal zeros corresponding to the ranks in the assertion.

Write $`x_-`$ for the old root and $`x_2`$ for the next root near $`-1`$. At $`x_-`$,

$$
 \frac{R^+(x_-)}{Bx_-}
   =\frac1{Bx_-}+(\alpha_1-1)x_-
     +\sum_{h\ge2}(\alpha_h-1)\beta_h x_-^h
   \sim \frac m{2j}>0.
$$

This strict sign retains the factor $`m/j`$ in the tail, even if the unweighted error is larger. On a fixed neighborhood of $`-1`$, the derivative of $`R^+(x)/(Bx)`$ is $`1+o(1)`$. The polynomial tail and its derivative are small there by the geometric bounds, and the Laurent correction has derivative $`O(B^{-1})`$. The mean value theorem gives $`x_--x_2\sim m/(2j)`$, while the other new reciprocal root tends to zero. Inverting the order gives the bracket and the relative gap.

## Transfer to a weaker growth condition

The carry argument itself needs only $`j/m\to\infty`$ together with the following coefficient inputs on $`e\ge j-1`$, uniformly over the degrees $`p\le m+1`$ used above. First, a relative log error $`O(1+m^2/j)=o(m)`$ in the coefficient formula $`a_p(e)=c_j^{p+1}V_j^p\binom{e+p}{p}\exp(O(1+m^2/j))`$, with normalization constants $`c_j,V_j`$ bounded above and below. Second, $`a_p(e+1)/a_p(e)=1+(p/(e+1))(1+o(1))`$ for $`p\ge1`$, and an exponentially small pole-remainder bound for $`p=0`$. The scale $`\rho`$ can be the true positive short-block pole $`\rho_j`$; the exact adjacent identities are unchanged.

Under these inputs the old normalized coefficient bound acquires a factor $`\exp(O((1+m^2/j)(h+1)))=\exp(o(mh))`$, preserving the geometric tail. The expression for $`B`$ acquires a factor $`\exp(o(m))`$ and bounded-base factors in $`m`$, so $`B^{-1}=o(m/j)`$ still follows. The increment formula preserves the signed gap. The [renewal argument](renewal.md) supplies these inputs and proves the order for every fixed number of outer ranks.
