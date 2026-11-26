# Concavity of the mean number of simultaneous column extensions

Write $a_k$ for the original balanced-array count at quota $k$, and $D=\lfloor nr/d\rfloor$. For $0\le k<D$ set

$$
u_k=(k+1)(a_{k+1}/a_k)^{1/d}.
$$

Then $u_k^d$ is the average number of ways to add one new cell in each column of a labeled feasible array of quota $k$. Indeed every array of quota $k+1$ admits $(k+1)^d$ independent choices of cells to delete, and all deletions preserve the row caps.

The candidate finite inequality is $2u_k\ge u_{k-1}+u_{k+1}$ at $1\le k\le D-2$. This asks about actual nonzero extensions on all three levels. For instance, with $n=4,d=2,r=1$, $u_0=\sqrt{12},u_1=\sqrt2$, and appending $u_2=0$ gives the opposite sign. At full cap $u_k=n-k$. At rank one $u_k=(\prod_{j=0}^{d-1}(n-dk-j))^{1/d}$. Strict concavity on the positive support follows from strict concavity of the geometric mean along this line when $d\ge2$. For a vector of positive affine functions with parallel equal nonzero slopes, differentiating twice reduces strictness to strict Cauchy–Schwarz for their reciprocals.

**Fixed-dimension theorem.** Fix $2\le r<d$. The finite inequalities are strict on every compact interior density interval for all sufficiently large $n$, uniformly on the interval. They are also eventually strict at each fixed positive quota and each fixed distance $D-k\ge2$ below saturation. The proof gives no finite universal row cutoff. Quotas approaching either boundary with the distance to the boundary diverging are outside these three assertions.

## Interior

Put $G(z)=\sum_{j=0}^r\binom dj z^j$, and choose $z=z(x)$ by $zG'(z)/G(z)=dx$, $x=k/n$. Let $w=(1-x)/x$ and $Y(w)=1/z(x)$. The [carried-load calculation](carried-load.md) proves $w=y+\delta(y)$ for $y=1/z$, with $w'>0$ and $\delta''(y)>0$ if $r\ge2$. A short independent strictness proof writes $\delta=1/U$ with $U$ a degree $r-1$ polynomial with positive log-concave coefficients. For the distribution with weights $[y^j]U$ tilted by $y^j$, the tails $T_j$ are log-concave: $T_{j+1}/T_j$ is the tail-weighted mean of successive mass ratios starting at index $j$, hence decreases. Thus $T_{a+b}\le T_aT_b$ for $a,b\ge1$. Summing and using strict inequality at $a=b=r-1$ gives $\mathbb E[J(J-1)]<2(\mathbb E J)^2$, which is $UU''<2(U')^2$. Consequently $Y''(w)<0$. The perspective $h(x)=xY((1-x)/x)$ satisfies $h''(x)=Y''(w)/x^3<0$.

The central coefficient expansion is, uniformly on any compact subinterval of $(0,r/d)$,

$$
\log a_k=n s(x)-\tfrac d2\log n+f_0(x)+n^{-1} f_1(x)+n^{-2}f_2(x)+O(n^{-3}),\qquad
s(x)=\log G(z)-dx\log z .
$$

Here the $f_j$ are smooth. To see the order of the error, tilt the single row to give a subset $S$ of size at most $r$ probability $z^{|S|}/G(z)$. Its mean is $x$ in every coordinate. Fourier inversion over $[-\pi,\pi]^d$ gives the centered sum probability multiplied by $G(z)^n z^{-dk}$. Uniformly on the compact set, all singletons and the empty subset have positive mass bounded away from zero. They give positive definite covariance, a strict characteristic-function gap away from the origin, and a Gaussian modulus bound near the origin. On the scaled Fourier ball $|t|\le n^{1/40}$ expand $n\log\phi(t/\sqrt n)$ through degree seven and expand the exponential in $n^{-1/2}$ through order five. The remainder, integrated against a fixed Gaussian majorant, is $O(n^{-3})$ after removing the factor $n^{-d/2}$. This follows from the bounded order-eight derivatives of the log characteristic function and Taylor's exponential remainder, bounded by $O(n^{-3})$ times a fixed polynomial in $|t|$ times the majorant. Odd powers integrate to zero by parity. The intermediate and outer regions are exponentially small in $n^{1/20}$. The leading Gaussian integral is bounded below on the compact set, so the logarithm has the stated expansion. Smoothness follows by differentiating its finite Gaussian moments and the analytic saddle equation.

Taking adjacent differences and exponentiating gives $u_k=n h(x)+h_0(x)+h_1(x)/n+O(n^{-2})$ with smooth $h_0,h_1$, since $s'(x)=-d\log z(x)$. The centered second difference of $u_k$ is $h''(x)/n+O(n^{-2})$. On the compact interval $h''$ is bounded strictly below zero in the sense $\max h''<0$.

## Both ends

At fixed $k$, write $p_k=a_k/\binom nk^d$. For independent uniform column subsets, a single row exceeds the cap with probability $\binom d{r+1}(k/n)^{r+1}+O(n^{-r-2})$. Two specified rows both exceed the cap with probability $O(n^{-2(r+1)})$: union bound over choices of $r+1$ occupied columns for each row and use the one- and two-label probabilities of a uniform $k$-subset. Consequently $\log p_k=-\binom d{r+1}k^{r+1}n^{-r}+O(n^{-r-1})$. Since $u_k=(n-k)(p_{k+1}/p_k)^{1/d}$, the leading term of $2u_k-u_{k-1}-u_{k+1}$ is $\binom d{r+1}\Delta^3(k-1)^{r+1}n^{1-r}/d$, which is positive. Here $\Delta^3(k-1)^{r+1}$ denotes the third forward difference of $t^{r+1}$ evaluated at $t=k-1$.

At fixed excess $e=nr-dk$, put $A_j=\binom dj$. For feasible residue classes,

$$
a_k=C_{d,r} A_r^n n^{e-(d-1)/2}\,(A_{r-1}/A_r)^e/e!\,(1+o(1)).
$$

The leading configurations have $e$ rows of size $r-1$ and all other rows of size $r$. After choosing the defective rows there are $A_{r-1}^e A_r^{n-e}$ possible arrays before imposing column balance. The balance probability is asymptotic to $C_{d,r} n^{-(d-1)/2}$, uniformly over the finitely many patterns in the defective rows. Apply lattice Fourier inversion to the first $d-1$ coordinates of the independent uniform $r$-subsets in the remaining rows. Differences of allowable subsets include every projected coordinate vector by exchanging that label with label $d$. Thus the distribution has full lattice span. Its covariance is $\lambda(I_{d-1}-\mathbf1\mathbf1^{\mathsf T}/d)$, where $\lambda=r(d-r)/(d(d-1))$, so $C_{d,r}=\sqrt d/(2\pi\lambda)^{(d-1)/2}$. A target at bounded distance from the mean gives the same leading Gaussian integral. The last column constraint follows from the total number of ones. Each other deficit profile uses at most $e-1$ defective rows and has the same $O(n^{-(d-1)/2})$ bound, so its contribution is lower order.

It follows that $u_k$ tends to $(r/d)(A_r/A_{r-1}) (e(e-1)\cdots(e-d+1))^{1/d}$ at a fixed admissible $e\ge d$. This function of $e$ is strictly concave for $e>d-1$. At a fixed $D-k\ge2$, the three quotas have excesses spaced by $d$, and the excess at the largest quota is at least $d$. The residue $nr\bmod d$ has only finitely many values, so strictness eventually holds across all rows.

## Consequence and remaining barrier

Finite extension concavity, together with orientation, would imply that the normalized curvatures $p_k^2/(p_{k-1}p_{k+1})$ increase with $k$. Indeed $u_{k+1}/u_k\le(n-k-1)/(n-k)$ by orientation. Writing $v=u_k-u_{k+1}$ gives $u_{k-1}u_{k+1}\le(u_k+v)(u_k-v)\le u_k^2(1-(n-k)^{-2})$. Therefore the successive ratios $p_{k+1}/p_k=(u_k/(n-k))^d$ are themselves log-concave, which gives the assertion at centers $1\le k\le D-2$ where all four probabilities are positive. Equivalently, $\Delta^3\log p_{k-1}\le0$. This is stronger than normalized log-concavity alone and restricts how fast coefficient curvature can fall on one side of a difficult quota.

The [integer-root screen](extension-concavity.py) read 1,659 distinct vectors from the pinned public archives, omitted the identically linear full caps, and certified all 14,570 internal inequalities it tested as strict. It took lower integer $d$th roots after scaling by $2^{256}$ and included the unit rounding error before deciding each sign. The general finite extension inequality and its application to all row caps remain open.
