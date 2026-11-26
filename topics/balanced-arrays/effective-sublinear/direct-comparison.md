# Direct comparison of balanced quotas at logarithmic dimension scale

Let $`u=\log n\ge10^6`$, $`100/u\le s=d/n\le1`$, and $`1\le r\le d`$. If $`k,k+1`$ are feasible quotas and both densities belong to $`[s/3,1-s/3]`$, then, with $`x_j=j/n`$ and $`L_j=(2\pi n x_j(1-x_j))^{-(d-1)/2}`$,

$$
\left|\log\frac{Q_{k+1}}{\sqrt d L_{k+1}}-\log\frac{Q_k}{\sqrt d L_k}\right|<n^{-1/8}.
$$

Here $`Q_j=a_j/U_j`$, where $`a_j`$ is the balanced coefficient and $`U_j`$ counts all row-capped labeled arrays with $`dj`$ ones in total. We work with scalar row-size profiles conditioned on this total, as in the [earlier coupling argument](../adjacent-quotas/comparison.md). Put $`\eta=n^{-1/4}`$. Regularity means $`|p_i-x|\le\eta`$, $`p_i=\ell_i/d`$. With $`A=\sum p_i(1-p_i)`$ and $`v=x(1-x)`$, one has $`A=nv-B`$, $`B=\sum(p_i-x)^2\le n\eta^2`$. Since $`v\ge2s/9`$ and $`\eta^2<s/50`$, the true Gaussian precision $`\lambda=dA/(d-1)`$ is at least $`d/5`$. Also $`d\ge100n/u\ge n^{.99}`$, since $`\log u\le .01u`$ for $`u\ge10^6`$.

## The fixed-profile coefficient after conditioning on each row sum

For row sizes as above, let $`P_{\ell}`$ be the probability of equal column sums under independent uniform row subsets, and put $`G=\sqrt d(2\pi\lambda)^{-(d-1)/2}`$. Write $`Y_j=(Z_j-\bar Z)/\sqrt\lambda`$ with independent standard Gaussians. Put $`Q_b(Y)=\sum Y_j^b`$. Using the summed subset cumulants in [the row expansion](direct-row-expansion.md), define

$$
\Phi=-\Gamma Q_3/6,\qquad \Pi=A_{\ast} Q_4/24+B_{\ast}Q_2^2/8,\quad m=\mathbb E\Pi,\qquad K_{\ell}=e^m\mathbb E\cos\Phi .
$$

We prove $`|P_{\ell}/G-K_{\ell}|<n^{-0.18}`$. The [off-chart estimate](direct-row-tail.md) bounds the relative torus contribution above column diameter $`\epsilon=n^{-2/5}`$ by $`n^{-10}`$. On the complementary set the zero-sum column lifts have $`M=\max|Y_j|\le\epsilon`$, and their quotient-coordinate Gaussian density is normalized by $`G`$. Indeed the fixed-last-column form for variance $`\lambda`$ has matrix $`\lambda(I_{d-1}-\mathbf1\mathbf1^{\mathsf T}/d)`$ of determinant $`\lambda^{d-1}/d`$. With column sum $`k`$ and total row size $`dk`$, the Fourier integrand is invariant under a common shift. The chart contains all centered real vectors of maximum modulus at most $`\epsilon/3`$. Thus the Gaussian chart failure probability is at most $`2d\exp[-\lambda\epsilon^2/18]`$.

On the chart the contribution is the real part of $`\mathbb E[\mathbf1_{\mathcal C}e^{i\Phi+\Pi+R}]`$, where $`|R|\le8\lambda Q_2M^3`$ and $`|\Re R|\le6\lambda Q_2M^4`$. Since $`\lambda\le n`$ and $`Q_2\le d\epsilon^2`$, $`|\Re R|\le6nd\epsilon^6<1`$. Under the Gaussian $`\lambda Q_2`$ is chi-square with $`d-1`$ degrees of freedom, of second moment $`d^2-1`$. Therefore $`\|R\mathbf1_{\mathcal C}\|_2\le8d\epsilon^3\le8n^{-1/5}`$.

The coefficient bounds $`|A_{\ast}|\le\lambda`$ and $`|B_{\ast}|\le2\lambda/d`$, together with $`Q_2^2\le dQ_4`$, imply $`2|\Pi|\le(7/12)\lambda Q_4`$. In the centered Gaussian coordinates $`T_j=Z_j-\bar Z`$, this is at most $`\sum_j T_j^4/\lambda`$. The event $`|\bar Z|\le1`$ is independent of the centered coordinates and has probability at least $`1/2`$. Insert it on the chart at cost at most two, use $`T_j^4\le8(Z_j^4+1)`$, and observe that $`|Z_j|\le1+\sqrt\lambda\,\epsilon\le2n^{1/10}`$. With $`t=8/\lambda`$, one has $`4tn^{1/5}\le1/4`$ since $`\lambda\ge d/5\ge n^{.99}/5`$. For a standard normal $`Z`$,

$$
\mathbb E[e^{t Z^4}\mathbf1_{|Z|\le2n^{1/10}}]\le 1+t\mathbb E[Z^4 e^{Z^2/4}]\le1+20t .
$$

The independent product gives $`\mathbb E[e^{2|\Pi|}\mathbf1_{\mathcal C}]\le2e^{21td}\le2e^{840}`$ because $`d/\lambda\le5`$. The row expansion gives $`|m|\le15/8`$, $`\|\Pi-m\|_2\le1.5\sqrt d/\lambda\le8/\sqrt d`$, and $`\mathbb E\cos\Phi\ge7/12`$. Hence $`1/16<K_{\ell}<8`$. Replacing $`e^{i\Phi+\Pi+R}`$ by $`e^{i\Phi+m}`$ on the chart has expected absolute error at most

$$
e^{422}\left(8n^{-1/5}+16/\sqrt d\right)
$$

by Cauchy–Schwarz, $`|e^z-1|\le |z|e^{\max(0,\Re z)}`$ and $`|e^z-e^m|\le |z-m|(e^{|z|}+e^{|m|})`$ for real $`z`$. Extending the last bounded integrand to the entire Gaussian incurs at most $`16d e^{-\lambda\epsilon^2/18}`$. This is less than $`n^{-10}`$ since $`\lambda\epsilon^2\ge n^{.19}/5`$ and $`u\ge10^6`$. Adding the torus tail proves the $`n^{-.18}`$ estimate. In particular it is valid at a feasible saturated endpoint.

## Comparing the fixed-profile factors under the monotone coupling

Couple neighboring scalar profiles by coordinatewise ordering. The two totals differ by $`d`$, so $`\sum_i|p_i'-p_i|=1`$. The cumulants vary regularly enough for this strong distance. For fixed $`d\ge10`$, regard the formulas in the row expansion as polynomials in $`p`$. Their derivatives on the interval $`[0,1]`$ satisfy

$$
|a'|\le2,\quad |\gamma'|\le5,\quad |(dB_4)'|\le20,\quad |A_4'|\le30 .
$$

Indeed $`dB_4= da((4d-6)a-(d-1))/((d-2)(d-3))`$, $`0\le a\le d/(4(d-1))`$ and $`A_4=a-6(a^2+B_4)`$. Thus the changes of $`\lambda,\Gamma,dB_{\ast},A_{\ast}`$ are bounded by $`2,5,20,30`$, respectively. Under joint regularity both precisions exceed $`d/5`$. Coupling the two Gaussians by the same centered standard normals, the cubic phases involve the same variable $`d^{-1/2}\sum T_j^3`$ of $`L^2`$ norm at most $`\sqrt6`$, multiplied by $`-\Gamma\sqrt d/(6\lambda^{3/2})`$. The change of this coefficient is below $`100/d`$ by the preceding bounds. To see this by differentiation along the segment of the two pairs $`(\Gamma,\lambda)`$, $`|\Gamma|\le\lambda`$ and $`\lambda\ge d/5`$ on the segment.

The exact quartic mean is

$$
m=\frac{A_{\ast}d(1-1/d)^2+B_{\ast}(d^2-1)}{8\lambda^2} .
$$

The same segment argument bounds its change by $`1000/d`$, since $`|A_{\ast}|\le\lambda`$, $`|dB_{\ast}|\le2\lambda`$ and the numerator changes by at most $`50d`$. The cosine expectations at either end exceed $`7/12`$. It follows that $`|\log K_{\ell'}-\log K_{\ell}|<2000/d`$. The corresponding log difference for the actual normalized fixed-profile probabilities $`P_\ell/G`$ is at most $`2000/d+64n^{-.18}`$.

Besides this factor, the scalar weight $`H_k(\ell)=P_\ell/(\sqrt d L_k)`$ consists exactly of the factor $`((d-1)/d)^{(d-1)/2}`$ and the determinant $`(1-B/(nv))^{-(d-1)/2}`$. The first factor is independent of $`k`$. If both profiles are regular, $`|B'-B|\le4\eta`$ by monotonicity and centering, $`B,B'\le n\eta^2`$, and $`|v'-v|\le1/n`$. With $`v,v'\ge s/5`$, $`B/(nv)<1/2`$, the change in the determinant log is at most $`20\eta+25\eta^2/s`$, by the derivative bound of $`-\log(1-z)`$ on this range. Hence the total regular-pair log difference is below $`n^{-1/6}`$ for $`u\ge10^6`$.

## Averaging the two profiles

The actual and scalar irregularity probabilities are bounded by $`t'=2n^2e^{-d\eta^2/2}`$ and $`t=2n(nd+1)e^{-2d\eta^2}`$ as in the earlier two-row and tilted-binomial estimates. Also $`((d-1)/d)^{(d-1)/2}\ge e^{-1/2}`$ and the determinant log is in $`[0,5B]`$. Thus $`1/40\le H\le10e^{5B}`$ on regular profiles; the fixed-profile lower bound $`K> (7/12)e^{-15/8}`$ leaves room in the constant. In particular $`W_k=\mathbb EH_k\ge1/80`$. The scalar second-moment calculation for $`H^2\mathbf1_{\rm regular}`$ costs at most $`100(nd+1)\exp(20 n/d)`$: for a single unconditioned tilted row $`S`$ the binomial Hoeffding bound gives $`\mathbb E e^{10(S/d-x)^2}\le1+20/(2d-10)`$. Since $`n/d\le u/100`$, this second moment is bounded by $`n^3`$. The fraction lost by requiring joint regularity is at most $`t'+80\sqrt{tn^3}<1/n`$ since $`d\eta^2\ge n^{.49}`$. Combining $`n^{-1/6}`$ with the two discarded log errors gives the stated comparison. $`\square`$
