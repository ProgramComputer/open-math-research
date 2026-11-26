# Fixed ranks at the large-modulus end when the cutoff grows at most linearly in the degree

Fix a positive constant $`C`$ and integer $`H\ge1`$. Consider $`n=mj+s`$ with $`0\le s<j`$, $`m,j\to\infty`$, and $`j\le Cm`$. The enumerator $`O_{n,j}(t)`$ sums over all ordered set partitions of $`[n]`$ and marks each block of size at least $`j`$. For each fixed number of exterior ranks, the roots of largest modulus are simple and negative, and their moduli satisfy the strict consecutive inequalities below. The estimates hold uniformly in $`s`$ once $`m`$ and $`j`$ are sufficiently large in terms of $`C`$ and the number of ranks. The bulk and the full conjecture remain unresolved. [Alexandersson’s conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions)

Write $`A_j=T_jU_j`$, where $`T_j(z)=1/(1-\sum_{1\le i<j}z^i/i!)`$ and $`U_j(z)=\sum_{i\ge0}j!z^i/(j+i)!`$. The reversed enumerator $`Q_{n,j}(y)=y^mO_{n,j}(1/y)/n!`$ has coefficients

$$
 b_h=(j!)^{-(m-h)}[z^{e_h}]F_{p_h}(z),\qquad
 p_h=m-h,\quad e_h=s+hj,\quad F_p=T_j A_j^p.
$$

Indeed the $`p`$ long blocks have $`p+1`$ ordered sequences of short blocks as gaps. Put $`y_h=b_h/b_{h+1}`$.

## The tilted coefficient estimate

For a series $`G`$ with nonnegative coefficients and constant term one, give $`X_{G,r}`$ probability $`[z^a]G\,r^a/G(r)`$ at $`a`$, and let $`X_{p,r}`$ be the independent sum of $`p+1`$ copies for $`T_j`$ and $`p`$ copies for $`U_j`$. Write $`L_p(a;r)=\Pr(X_{p,r}=a)`$ and $`\mu_p(r)=\mathbb E X_{p,r}`$. Then

$$
 [z^a]F_p=F_p(r)r^{-a}L_p(a;r).
$$

For $`0\le h\le H+1`$ and $`e_h>0`$, let $`r_h`$ be the unique radius with $`\mu_{p_h}(r_h)=e_h`$. It lies in $`0<r_h<R<\log 2`$ with a fixed $`R`$ depending only on $`C,H`$. In fact, on compact subsets of $`r<\log2`$, $`T_j\to (2-e^r)^{-1}`$ together with its derivatives. Choose $`R<\log2`$ where the limiting log derivative $`R e^R/(2-e^R)`$ exceeds $`2(H+2)C+1`$, then use $`p_h\sim m`$. Positivity of variance ensures strict increase of the mean. When $`e_h=0`$ adopt $`r_h=0`$.

For bounds uniform near zero, fix $`R<R_1<R_2<\log 2`$. For each summand the exponential moments are uniformly bounded at $`r\le R_1`$ for changes of log-radius of magnitude at most $`\epsilon>0`$, choosing $`R_1e^\epsilon\le R_2`$. Each raw moment of fixed positive integer order $`d`$ is $`O(r)`$. Coefficientwise, $`T_j(z)`$ is bounded by $`(2-e^z)^{-1}`$ and $`U_j(z)`$ by $`e^z`$. For either comparison series $`G`$, the sum $`\sum_{a\ge1}a^d[z^a]G(z)R_2^{a-1}`$ is finite. Factor out $`r`$ from the corresponding tilted moment numerator and use this finite sum. The denominator is at least one. For the $`T_j`$ summands the masses at 0 and 1 are at least $`c`$ and $`cr`$ respectively, since their coefficients are both one and $`T_j(r)`$ is bounded. These give the mean lower bound. For the variance lower bound, use $`\mathrm{Var}(X)=\mathbb E(X-X')^2/2`$ with $`X'`$ an independent copy and retain the events $`(X,X')=(0,1),(1,0)`$. Consequently the mean and variance of $`X_{p_h,r}`$ are both of order $`mr`$, uniformly on $`0<r\le R_1`$, and $`r_h\asymp e_h/m`$. The third absolute centered moments of the summands sum to $`O(mr)`$.

For $`e_h\to\infty`$, locally at $`a=e_h+O(1)`$ one has, uniformly in the prescribed parameters,

$$
 L_{p_h}(a;r_h)=\frac{1+o(1)}{\sqrt{2\pi\mathrm{Var}(X_{p_h,r_h})}}.
$$

The characteristic function of each $`T_j`$ summand has modulus at most $`\exp(-c r_h(1-\cos\theta))`$, by retaining the pair of masses at 0 and 1 in the squared modulus identity. Thus the full characteristic function is bounded by $`\exp(-c' e_h\theta^2)`$ for $`|\theta|\le\pi`$. For $`\theta=v/\sigma`$ and $`\sigma^2=\mathrm{Var}(X_{p_h,r_h})`$, expand the logarithm of each centered characteristic function near one. The summed quadratic term is $`-v^2/2`$ and the error is $`O(e_h|\theta|^3+e_h\theta^4)`$ for bounded $`v`$. Indeed the third absolute centered moments sum to $`O(e_h)`$, each variance and third absolute centered moment is $`O(r_h)`$, and the error from taking logarithms is bounded by a constant times the sum of squared deviations of the individual centered characteristic functions from one. This gives the Gaussian limit uniformly on fixed compact $`v`$-intervals. Under that scaling the phase from $`a-e_h=O(1)`$ converges to one. Fourier inversion and the integrable Gaussian domination establish the display, also when $`e_h/m\to0`$.

For bounded $`e_h`$, expand $`\exp(p_h\log A_j)T_j`$ through this fixed degree. The coefficient is a polynomial in $`p_h`$ with leading contribution from $`e_h`$ linear factors of $`\log A_j`$, giving

$$
 [z^{e_h}]F_{p_h}\sim \frac{p_h^{e_h}}{e_h!}\left(1+\frac1{j+1}\right)^{e_h}.
$$

The lower-order coefficients are uniformly bounded in $`j`$ at each fixed degree by the coefficient bounds and the formal logarithm formula. The same applies at $`e_h+1`$. When $`e_h>0`$ is bounded, $`mr_h\asymp e_h`$ and $`F_{p_h}(r_h)\le \exp(O(mr_h))`$ by integrating its log derivative. The coefficient formula then gives $`L_{p_h}(e_h;r_h)\gg1`$. At $`r_h=0`$ the law is a point mass. These facts together give a uniform lower bound on saddle masses by a constant times $`(e_h+1)^{-1/2}`$.

## Exponential separation, including the full coefficient tail

Set $`D(r)=j!/(r^j A_j(r))`$. The exact coefficient identity gives, at any $`r>0`$,

$$
 y_hD(r)=\frac{L_{p_h}(e_h;r)}{L_{p_{h+1}}(e_{h+1};r)} .
$$

At $`r_{h+1}`$, the law in the denominator is centered while the mean in the numerator is at least $`e_{h+1}=e_h+j`$ because $`F_{p_h}=F_{p_{h+1}}A_j`$. A fixed small negative log-radius change proves
$`L_{p_h}(e_h;r_{h+1})\le e^{-c j}`$ for $`c=c(C,H)>0`$. To see the uniform bound, the second log-radius derivative of the log moment generating function is the variance evaluated at the changed radius, $`O(mr_{h+1})=O(j)`$, so Taylor's bound in the Chernoff exponent is $`-\epsilon j+O(\epsilon^2j)`$. Thus $`y_hD(r_{h+1})\le O(\sqrt j)e^{-cj}`$. The factor $`D(r)`$ for advancing one place in the reversed row is exact, and positivity bounds each tilted mass by one. Hence for every $`l\ge1`$ such that a coefficient exists,

$$
 \frac{b_{h+1+l}y_h^{h+1+l}}{b_{h+1}y_h^{h+1}}
 \le O(\sqrt j)(y_hD(r_{h+1}))^l .
$$

For the other direction, if $`h\ge1`$, use $`r_h`$. At that radius $`X_{p_{h+1},r_h}`$ has mean at most $`e_h`$, so $`L_{p_{h+1}}(e_{h+1};r_h)\le e^{-cj}`$ by the same argument with a positive log-radius change. It yields

$$
 \frac{b_{h-l}y_h^{h-l}}{b_hy_h^h}
 \le O(\sqrt j)(y_hD(r_h))^{-l},
 \qquad (y_hD(r_h))^{-1}\le O(\sqrt j)e^{-cj}.
$$

This tail is empty for $`h=0`$. These bounds use a single tilt per side and include all remaining degrees. In particular $`y_h/y_{h+1}\le e^{-c'j}`$ for some $`c'>0`$ by taking $`l=1`$ on the first side and absorbing polynomial factors.

Rescale $`y=y_h z`$ and divide $`Q_{n,j}(y_hz)`$ by $`b_hy_h^h`$. The central terms are $`z^h(1+z)`$. The two bounds imply that, uniformly on $`1/2\le |z|\le2`$, the other terms divided by $`|z|^h`$ are $`O(e^{-c''j})`$. Rouché on $`|z+1|=e^{-c''j/2}`$ gives a unique simple negative zero there, using conjugation. On $`|z|=1/2`$ and $`|z|=2`$ it gives respectively $`h`$ and $`h+1`$ roots inside the contour. Thus this is the root of rank $`h+1`$ in increasing reciprocal modulus, or decreasing original modulus. The relative error between the modulus and $`y_h`$ is exponential. The same applies to any fixed finite number of the stated ranks and works without assuming real-rootedness elsewhere.

## Consecutive motion and degree rollover

At fixed $`m`$ an increment of $`n`$ increments both residuals in $`y_h`$ by one, with $`p_h,p_{h+1}`$ fixed. If $`e_h\to\infty`$, the local estimate gives

$$
 \frac{y_h(n+1)}{y_h(n)}=(1+o(1))\frac{r_{h+1}}{r_h}.
$$

The ratio $`r_{h+1}/r_h`$ is bounded uniformly away from one. Indeed $`\mu_{p_h}(r_{h+1})\ge e_h+j`$, while $`\mu_{p_h}'\le C_1m`$ throughout the compact radius interval from the variance upper bound divided by $`r`$. Thus $`r_{h+1}-r_h\ge j/(C_1m)`$, while $`r_{h+1}\le C_2 j/m`$. If $`e_h`$ is bounded, the elementary adjacent coefficient ratio for the numerator is asymptotic to $`m/(e_h+1)`$ and the denominator ratio is $`(1+o(1))/r_{h+1}`$, so $`y_h(n+1)/y_h(n)\to\infty`$. Uniformity over all residuals follows by applying these complementary cases to subsequences.

The factor $`y_h(n+1)/y_h(n)`$ is $`O(j)`$. For $`e_h\to\infty`$, compare the two radii with $`e_h/m`$ and $`(e_h+j)/m`$. For bounded $`e_h`$, use the adjacent coefficient asymptotics. Thus the fixed-rank negative roots move strictly toward zero in the original variable and their motions preserve order relative to the next old rank, by the exponential separation. This applies in both directions because all root errors are exponentially small.

Let $`\rho_h(n)`$ denote the modulus of the reciprocal root at rank $`h+1`$. For every $`0\le h<H`$, the equal-degree estimates give

$$
 \rho_h(n)<\rho_h(n+1)<\rho_{h+1}(n).
$$

The first inequality uses the uniform strict factor in the motion. The second follows from $`y_h(n+1)/y_h(n)=O(j)`$ and $`y_h(n)/y_{h+1}(n)\le e^{-c'j}`$. At the degree increase the inequalities for the same range of $`h`$ are

$$
 \rho_0(n+1)<\rho_0(n),\qquad
 \rho_h(n)<\rho_{h+1}(n+1)<\rho_{h+1}(n).
$$

At $`s=j-1`$, the balance $`y_{h+1}(n+1)`$ uses exactly the same two values $`p_h,p_{h+1}`$ as $`y_h(n)`$ and increments both residuals by one. The same comparisons therefore give $`y_{h+1}(n+1)>y_h(n)`$ by a fixed factor bounded away from one, with ratio at most polynomial in $`j`$. The extra new balance $`y_0(n+1)`$ is exponentially smaller than $`y_1(n+1)`$, and hence than $`y_0(n)`$. For the second displayed rollover inequality use $`y_{h+1}(n+1)=O(j)y_h(n)`$ and the old-row exponential separation. Returning to the negative original roots preserves the order shown because $`-\rho^{-1}`$ is increasing in $`\rho`$. In the original variable the extra new extreme root lies beyond the old extreme, and the other old and new roots alternate through each fixed number of the outer ranks. For fixed $`m`$ the analogous alternating order begins with the old extreme root.

The proof covers fixed exterior ranks and diverging $`m,j`$ in the regime $`j\le Cm`$.
