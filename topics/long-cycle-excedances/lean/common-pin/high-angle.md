# An exact-truncation high-angle sign bound

Let $k\ge7$, $x\ge0$ and $t=-e^{-x}$. Put $w_p=x+ip\pi$ for odd integers $p$,
$r=|w_1|$, $S=\pi/r$, $c=x/r$, and $z=r/w_1=c-iS$.
Assume $S\ge 1/2$ and $n\ge 100k\log k$.
Use $T=\exp G$ with $G$ from the cutoff logistic coefficient identity,
and let $\tau_j$ denote its Taylor coefficients at zero.

For each positive integer $q$, write $C_q=E_{q,k}(t)/(q!(1-t)^{q+1})$.
The exact positive-order pole moment identity, with the order-zero logistic
coefficient read separately, gives

$$
C_q=\frac{\tau_q}{1-t}+\sum_{p\text{ odd}}\sum_{j<q}
       \frac{\tau_j}{w_p^{q-j+1}}.
$$

The finite sum can be moved inside the pole sum because each exponent is at
least two. This is the coherent common coefficient identity. The truncation
for $q=n+1$ can also be written with $j<n$ and the extra $j=n$ term outside.

Choose $R=r(1+1/k)$ and $\rho=r/R$. The linear coefficient $g_1$ of $G$ is
$-t/(1-t)\le1/2$. Its weighted size is therefore at most five, since
$r\le2\pi<8$ and $k\ge7$. For $2\le \ell<k$ the weighted higher coefficient
is bounded by

$$
|g_\ell|R^\ell\le
\frac{(1+1/k)^\ell}{\ell}\sum_{p\text{ odd}}(r/|w_p|)^\ell
\le\frac{18}{\ell}.
$$

Indeed, the first two pole terms contribute two in the square sum, and the
other terms contribute at most $8\sum_{p\ge3}p^{-2}\le4$ by the reciprocal
telescoping bound. Higher powers only decrease these terms.
Also $(1+1/k)^\ell\le e<3$. Thus the weighted absolute coefficient mass of
$G$ at $R$ is at most $5+18\log k$, using
$1/j\le\log j-\log(j-1)$ for $j\ge2$.

The coefficient convolution for $\exp G$, or its product of finitely
many monomial exponentials, gives $|\tau_j|\le A R^{-j}$ where
$A=\exp(5+18\log k)$. This follows by taking absolute values in the
monomial exponential factors and evaluating the resulting nonnegative
coefficient series at $R$. At the principal pole,
$|T(w_1)|=e^{\mathrm{Re}G(w_1)}\ge A^{-1}$. Write $M=|T(w_1)|$.
The real parts of conjugate terms give the nearest-pair sum.

Normalize the row by setting $Y_q=r^{q+1}C_q/(2M)$ and
$a_q=T(w_1)z^{q+1}/M$. Then

$$
|Y_q-\mathrm{Re}a_q|
\le\frac{A}{M}\left((k+1)\rho^q+10\rho^{q-1}+4\rho^q\right).
$$

The three contributions are the following.

- The omitted principal Taylor tail has sum at most
  $A\rho^q/(1-\rho)=A(k+1)\rho^q$ at each principal pole.
- For each far pole the geometric convolution gives
  $A/(R^{q-1}|w_p|^2(1-R/|w_p|))$ before normalization. Since
  $|w_p|\ge 3r/2$, its ratio $R/|w_p|$ is at most $16/21<4/5$.
  The sum of $r^2/|w_p|^2$ over both far half-lattices is at most four.
  This gives the coefficient ten after division by two.
- The order-zero logistic term is bounded by $4 A\rho^q$ after
  retaining the factor $1/M$, using $r/2\le4$ and $1/(1-t)\le1$.

For $q=n,n+1$ we have $\log(1+1/k)\ge1/(2k)$ and $k+15\le4k$. Therefore the
displayed error is at most
$4e^{10}k^{37}e^{-(n-1)/(2k)}\le4\cdot3^{11}k^{-13}<1/6$.

At an actual old zero $E_{n,k}(t)=0$ we have $Y_n=0$. Since $|a_n|=1$,
$|\mathrm{Re}a_n|\le 1/6$ and $|\mathrm{Im}a_n|>2/3$.
The consecutive principal part is
$\mathrm{Re}(a_n z)=c\mathrm{Re}a_n+S\mathrm{Im}a_n$.
The absolute error consisting of the first summand and the new-row
remainder is at most $1/3$, strictly below $S|\mathrm{Im}a_n|$.
Consequently

$$
Y_{n+1}\mathrm{Im}a_n>0.
$$

The normalizing factor for $Y_{n+1}$ is positive. The actual reduced next
row has the opposite sign, because $t<0$.

The formal sign statement uses the unnormalized imaginary principal part
$\mathrm{Im}(T(w_1)z^{n+1})$. Its product with the literal next
permutation row is positive at every qualifying old zero. Finding and
counting these zeros, and establishing the required signs at smaller
pole angles or lower ratios of $n$ to $k\log k$, require further estimates.
[Formal sign source](ActualHighAngleSign.lean) · [Common coefficient identity](RepositoryCoherentPoles.lean)
