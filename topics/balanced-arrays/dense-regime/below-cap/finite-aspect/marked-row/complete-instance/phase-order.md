# Nested marked-row slices and a lower curvature bound

Use $`n=10^6,d=250000,r=127000`$. This argument covers every geometric index $`507300\le k\le507905`$. Write $`C(\boldsymbol q)`$ for the labeled-array count with column quotas $`\boldsymbol q`$ and $`P(\boldsymbol q)=C(\boldsymbol q)/\prod_h\binom n{q_h}`$. The normalized extension loss in column $`i`$ is $`e_i(\boldsymbol q)=\Pr(|X|=r\mid X_i=0)`$ for a specified row $`X`$ of a uniform array in this fiber. The insertion identity gives $`P(\boldsymbol q+\boldsymbol e_i)/P(\boldsymbol q)=1-e_i(\boldsymbol q)`$. The orientation theorem gives coordinatewise monotonicity of each loss. [Orientation theorem](../../../../../orientation-normalization.md) · [Insertion identity](../paper.pdf)

Compare each phase of the path from equal quota $`k-1`$ to equal quota $`k`$ with the corresponding phase of the path from $`k`$ to $`k+1`$. The base margins in the first phase are $`\kappa=k-1`$ or $`\kappa+1`$, and every coordinate in the second base is larger by one. Write $`N=n-1`$ for the residual height after setting aside a marked row. Every residual fiber used here is feasible. To see this, its total is at most $`d(k+1)\le(n-2)r`$, its quotas are between zero and $`n-2`$, and successive columns can occupy successive cyclic blocks of row labels.

## 1. Swapping two marked columns

When the marked row occupies a subset $`S`$, its unnormalized probability is the residual completion count $`f(S)=C_{N}(\boldsymbol q-\mathbf 1_S)`$. We use this identity both with all columns available and conditional on $`X_i=0`$, when available columns exclude $`i`$. Consider interchanging a marked low-quota column with an unmarked high-quota column. In the residual array the new selected pair of columns has equal margins $`\kappa,\kappa`$. Before the interchange its margins were $`\kappa+1,\kappa-1`$. All other residual margins remain fixed.

In the uniform equal-pair fiber, let $`Y`$ be the number of rows of type $`10`$ in those columns, which equals the number of rows of type $`01`$. Fix the other columns and the sum of the selected two cells in each row. The $`2Y`$ singleton positions can be assigned in $`\binom{2Y}{Y}`$ ways in the equal fiber and $`\binom{2Y}{Y+1}`$ ways in the unequal one. The latter is zero if $`Y=0`$. The row caps hold on all assignments because each row sum is fixed. Every pattern possible in the unequal fiber is also possible in the equal one. Thus the ratio of unequal to equal counts is $`\mathbb E[Y/(Y+1)]`$.

Here is a finite bound uniform over all the choices of the other margins. Let $`W_y`$ count the equal-fiber arrays with $`Y=y`$. There are $`\kappa-y`$ rows of type $`11`$ and $`N-\kappa-y`$ rows of type $`00`$. In a third column $`j`$, let $`b_j`$ and $`a_j`$ count its ones among those two sets respectively, with $`b_j`$ referring to $`00`$. Its margin is at most $`\kappa+1`$, hence at least $`b_j-y-1`$ of the $`11`$ rows miss $`j`$. Select a $`00`$ row containing $`j`$ and a $`11`$ row missing $`j`$. Exchange their entries in the first selected column and in column $`j`$. This increases $`Y`$ by one and preserves all row and column sums. There are at least $`\sum_j b_j(b_j-y-1)`$ forward choices. For any array at $`y+1`$ the number of inverse choices is at most $`(d-2)(y+1)^2`$.

Put $`m=\lfloor7N/100\rfloor`$, $`M=\lfloor8N/100\rfloor`$ and $`s_0=nr-d(507300-1)`$. The total deficit of the residual array is at most $`s_0`$, because removing the marked row removes a nonnegative deficit. For $`y\le M`$, the sum of $`b_j`$ is at least $`r(N-507904-M)-s_0`$. The rational verifier checks, with $`B=[r(N-507904-M)-s_0]/(d-2)`$, that $`B>M+1`$ and $`B(B-M-1)\ge3(M+1)^2`$. Cauchy–Schwarz and the two counts of switches yield $`W_{y+1}\ge3W_y`$ for $`0\le y<M`$. Therefore

$$
\mathbb E[(Y+1)^{-1}]\le \frac{1}{m+1}+\frac{3^{m-M}}{2}\le \frac{1}{m+1}+\frac{1}{2\cdot3^{18}}=:\epsilon .
$$

The verifier checks $`(1-\epsilon)^{-1}\le1+4/d`$. In particular on every fixed-size marked-row slice, replacing a low mark by a high one changes the individual completion weight by a factor in $`[1,1+4/d]`$.

## 2. Coupling successive sizes by inclusion

Write $`H,L`$ for the numbers of available high and low columns and $`F(a,b)`$ for the completion count with $`a`$ high and $`b`$ low marks. The mass of $`a`$ at total size $`j`$ is proportional to $`V_j(a)=\binom Ha\binom L{j-a} F(a,j-a)`$. In the common interior of the two supports, with $`b=j-a`$, the ratio

$$
\frac{V_{j+1}(a+1)/V_{j+1}(a)}{V_j(a+1)/V_j(a)}
$$

is the product of $`(1+1/b)(1+1/(L-b))`$ and a quotient of two single-swap factors from the preceding section. The first factor is at least $`1+4/L`$ by the arithmetic-harmonic mean inequality, while the second is at least $`(1+4/d)^{-1}`$. Hence the high count increases stochastically with the size. Indeed the ratio of the two probability masses increases on their common support, and the endpoints of the integer support also move to the right or stay fixed. The same proof interchanging high and low gives stochastic increase of the low count. The reciprocal swap factors have the same bound on their relative range. If either class is empty, the only changing count is deterministic.

Using one uniform quantile to couple the two high counts, these two stochastic orders put $`A_j\le A_{j+1}\le A_j+1`$. The second inequality follows by writing the low count as $`j-A_j`$. Taking prefixes of fixed random permutations in each class then couples the marked subsets by inclusion. This holds for both the full marked row and the row conditioned on missing the next column. In the full row it implies $`\Pr(X_i=0\mid |X|=j)`$ is nonincreasing in $`j`$. Consequently $`\mathbb E[r-|X|\mid X_i=0]\ge r-\sum_h q_h/n`$, by the covariance inequality for two functions monotone in the same direction.

## 3. A signed difference between consecutive extension losses

Use a superscript $`+`$ for the base $`\boldsymbol q+\mathbf1`$. On subsets missing $`i`$, the ratio of completion weights upon adding $`h`$ is

$$
\frac{f(S\cup\lbrace h\rbrace )}{f(S)}=\frac{q_h}{n-q_h}\frac{1}{1-e_{\mathrm{res},h}} .
$$

The residual base is $`\boldsymbol q-\mathbf1_{S\cup\{h\}}`$ at height $`n-1`$. In the plus fiber the whole residual base increases by one, so its loss factor increases by orientation. The log increment in raw odds is at least $`1/(q_h+1)+1/(n-q_h)\ge\delta=4/(n+1)`$, using $`\log(1+x)\ge x/(1+x)`$. Thus $`f^+(S)/(e^{\delta|S|}f(S))`$ is nondecreasing under inclusion. The size-conditioned coupling shows that the conditional mean of this ratio is nondecreasing in the size. These means are precisely the unnormalized size likelihood ratios of the plus law to the exponentially tilted original law. In particular its top probability is at least the tilted top probability.

Set $`U=r-|X|`$ in the original row conditional on $`X_i=0`$, and write $`e=e_i(\boldsymbol q)`$. We obtain $`e_i(\boldsymbol q+\mathbf1)\ge e/\mathbb E e^{-\delta U}`$. On $`[0,r]`$ concavity gives $`1-e^{-\delta U}\ge U(1-e^{-\delta r})/r`$. Applying $`1/x-1\ge1-x`$ for $`0<x\le1`$ yields

$$
e_i(\boldsymbol q+\mathbf1)-e_i(\boldsymbol q)
\ge e [r-dk/n] (1-e^{-\delta r})/r.
$$

The same lower bound holds for the increase of $`-\log(1-e_i)`$. Orientation gives $`e\ge e(n,k-1)`$, the balanced loss at the start of the phase. Multiplying the normalized extension ratios along both paths, then restoring the raw binomial factors, gives the diagonal estimate

$$
\log\frac{a_k^2}{a_{k-1}a_{k+1}}
\ge \frac{4d}{n+2} + d e(n,k-1)(r-dk/n)\frac{1-e^{-\delta r}}{r}.
$$

To lower-bound $`e(n,k-1)`$ put $`s=nr-d(k-1)`$, $`c=d-r`$, $`R=rc/d`$ and $`\alpha=cn/[d(n-k+1)]`$. The row-deficit theorem bounds the saturation probability in the balanced fiber from below by $`(n-1)(1-\Delta)/(n+s-1)`$, where one may take

$$
\Delta=\frac{s(s-1)}{R n(n-1)}+\frac{s}{nR}+\frac{2s}{nr}.
$$

The conditional probability $`e(n,k-1)`$ equals $`\alpha`$ times the saturation probability by exchangeability. The checker also allows the second, independently proved, bound for $`\Delta`$ from the same theorem. [Row-deficit inequality, “How many rows can accept an entry?”](../../upper-edge/paper.pdf)

Integer arithmetic and Taylor lower sums show $`e(n,k-1)(r-dk/n)>0.4986304`$ throughout the 606 indices and $`\log(a_k^2/(a_{k-1}a_{k+1}))>1.39095364>\log 4`$. This proves the strict geometric sign at each of these indices: the two first neighbors relative to the central term have equal magnitude strictly below $`1/2`$, and both later alternating tails beginning at distance two are nonnegative by log-concavity. [Exact numerical checks](phase_order.py)
