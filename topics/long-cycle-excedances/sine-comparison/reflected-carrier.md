# Pairing the logarithms of opposite signed poles

In the [adjacent sine comparison](README.md), let $k\ge2$, $n\ge10000$, $n\le48k$, $S=\sin\theta>0$ and $nS^2\ge6/5$. Write $w_q=\cos\theta+i(2q+1)S$, with the distinguished pole indexed by $q=0$. The index $q=-1$ is its conjugate. Let $P$ be the product over $q\ne0$ of the actual occupied factors evaluated at $w_0$. With $H_m=\sum_{i=1}^m1/i$, the scaled principal contribution satisfies

$$
2k e^{-H_{k-1}}\Re P>\frac{6000}{12243}.
$$

For $n\le10k$ the stronger lower bound is $54/55$. The two estimates require eleven positive-index terms each. The [formal result](../lean/paired-profile/PrincipalScaledBudget.lean) refers to the literal occupied primitives of the cycle series. The [infinite-product identity](../lean/paired-profile/PrincipalLatticeProduct.lean) includes the conjugate endpoint.

**Reflection.** Set $r=k-1$. The radial logarithm of the $q$th factor has norm at most $|w_q|^{-r}/(2|q|rS)$. The term $q=-1$ therefore contributes at most $1/(2rS)$. Pair $q=t$ with $q=-(t+1)$ for $t\ge1$. Their squared denominators are equal to $1+4t(t+1)S^2$. The [Bernoulli estimate](../lean/sine-comparison/PrimitivePoleKernel.lean) implies $|w_t|^{-r}\le(1+ht(t+1))^{-96}$ if $192\le r$ and $40h\le r/n$. The dimension bounds here imply $r\ge192$. If $A\le rS$, the sum of all logarithm norms is at most

$$
\frac1{2A}\left(1+\sum_{t\ge1}W_h(t)\right),\qquad W_h(t)=\frac{1/t+1/(t+1)}{(1+ht(t+1))^{96}}.
$$

For $t\ge L\ge1$, keep 95 factors of the denominator at their value for $t=L$. Bound the last factor below by $ht(t+1)$. The identity $(1/t+1/(t+1))/(t(t+1))=1/t^2-1/(t+1)^2$ gives

$$
\sum_{t\ge L}W_h(t)\le\frac{1}{hL^2(1+hL(L+1))^{95}}.
$$

**Rational bounds.** For $n\le Xk$, we have $r/n\ge1/X-1/10000$ and $nS\ge\sqrt{12000}>5477/50$. Take $(h,A)=(1/405,109/10)$ at $X=10$ and $(1/1940,227/100)$ at $X=48$. Both choices satisfy the stated inequalities. With $L=12$, the corresponding logarithm budgets round upward to $99911/10^6$ and $799556/10^6$. The local formal proof rounds each of the eleven terms and the tail up separately and proves budgets $1/10$ and $4/5$. The disk bound on $\Re(e^z)$ then gives $e^{-1/10}$ and $e^{-4/5}$. [Tail theorem](../lean/paired-profile/ReflectedLogTail.lean) · [Termwise certificates](../lean/paired-profile/ReflectedLogBudget.lean) · [Signed-lattice reindexing](../lean/paired-profile/ReflectedLogSum.lean) · [Original-product bounds](../lean/paired-profile/PrincipalBudgetJoin.lean)

For the harmonic normalization, $H_{20}<18/5$ by rational arithmetic. The inequality $1/(m+1)\le\log(m+1)-\log m$ telescopes to $H_m\le18/5+\log(m/20)$ for $m\ge20$. Thus $2k e^{-H_{k-1}}>12/11$, using $e^{18/5}<110/3$. Using $e^{1/10}<10/9$ and $e^{4/5}<1113/500$ now gives both scaled principal bounds. [Formal harmonic estimate](../lean/paired-profile/PrincipalHarmonic.lean)

**Consequence for the written determinant proof.** Substitute these two lower bounds for the principal contribution in the [reviewed four-error comparison](uniform-carrier.md). Reusing its four upward-rounded error bounds in each aspect interval gives $kD_n/S>325873/10^6$ on $4\le n/k\le48$. The smallest certified margin occurs in the final interval. This consequence uses the written estimates for the other terms. The local Lean check covers the principal contribution. The Lean 4.33.1 replay of this package is pending. [Exact calculation](check-reflected.py) · [All nine margins](reflected-output.txt)
