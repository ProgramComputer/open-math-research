# Nearly empty rows, uniformly in the cap

Let $`1\le r<d`$, $`d\to\infty`$, and let the row-size law be proportional to $`\binom ds w^s`$ on $`0\le s\le r`$. Write $`\mu=\mathbb E S`$, $`V=\mathrm{Var}(S)`$ and $`H(w)=\sum_{s\le r}\binom ds w^s`$. The following two estimates use constants independent of $`r`$.

## Two principal phases at small mean

If $`0<\mu\le1/10`$ and $`n\mu/d^2\to\infty`$, the torus integral of the normalized row function to the power $`n`$ at the negative argument $`-w^d`$ has the same two-saddle formula as in the interior estimate. In detail, write $`\phi=\pi/d`$, $`G(s)=s(d-s)/(d(d-1))`$, $`\lambda_t=\mathbb E[G(S)e^{itS}]/\mathbb E e^{itS}`$, and $`\nu=(d-1)/2`$. Its value is

$$
\frac{2}{\sqrt d}(2\pi n)^{-\nu}
\mathrm{Re}\negthinspace \left[(\mathbb E e^{i\phi S})^n\lambda_\phi^{-\nu}\right]
+o\negthinspace \left(\frac{|\mathbb E e^{i\phi S}|^n}{\sqrt d}(2\pi n|\lambda_\phi|)^{-\nu}\right).
$$

We detail the uniformity needed for the moving-tilt and transverse integration lemmas. Write $`a=dw=p_1/p_0`$ where $`p_j=\mathbb P(S=j)`$. Since $`p_0\ge1-\mu`$ and $`p_1\le\mu`$, $`a\le1/9`$. The bounds $`p_s\le a^s/s!`$ and $`p_1\ge(9/10)a`$ imply $`a\asymp\mu`$, $`p_1\asymp\mu`$, $`V\asymp\mu`$ and $`\mathbb E S^m\le C_m\mu`$ for each fixed $`m\ge1`$. Also $`V=\mu+O(\mu^2)`$ as $`\mu\to0`$. For each $`t`$, $`|\mathbb E e^{itS}|\ge1-2\mu\ge4/5`$. The empty support and each singleton give the angular bound

$$
|R(\theta)/H(w)|\le\exp\negthinspace \left[-c\thinspace \frac{\mu}{d}\sum_{j=1}^d|e^{i\theta_j}-1|^2\right],
\qquad R(\theta)=\sum_{|A|\le r}w^{|A|} e^{i\sum_{j\in A}\theta_j}.
$$

Indeed these terms in the squared characteristic modulus give a loss $`p_0p_1 d^{-1}\sum_j|e^{i\theta_j}-1|^2`$. Outside a fixed small arc around zero in any coordinate, retain half its exponential loss and integrate the remaining $`d-1`$ free circle variables (eliminating a different coordinate). The absolute bound, divided by $`H(w)^n`$, is $`d e^{-c n\mu/d}(C d/(n\mu))^{(d-1)/2}`$. At the principal phase $`|\mathbb E e^{i\phi S}|\ge e^{-C\mu/d^2}`$ and $`\lambda_0\asymp\mu/d`$ using singleton mass and $`G(s)\le s/d`$. Thus the off-arc bound is negligible relative to one saddle whenever $`n\mu/d^2\to\infty`$.

Inside the arc, the first $`d-1`$ independent angles determine the odd common phase $`t=(2j+1)\pi/d`$ by averaging all lifted coordinates. Write the zero-sum deviations as $`y`$. The moment bounds used in the fixed-cap local and global integral estimates hold with constants independent of $`r`$. Namely, for $`L=\sum_{j\in I} y_j`$ at a uniform size-$`S`$ support $`I`$,

$$
\mathbb E[S^l|L|^m]\le \frac{\mathbb E S^{m+l}}{d}\sum_j|y_j|^m
\le C_{m,l}\frac{\mu}{d}\sum_j |y_j|^m
\qquad(m\ge1,\ l\ge0).
$$

The first inequality conditions on $`S`$ and uses convexity. The same inequalities bound any fixed number of derivatives in $`t`$ of the complex-tilted moments, since the denominator stays above $`4/5`$. In particular $`\mathrm{Re}\lambda_t=\lambda_0(1+O(t^2))`$, the cubic term is $`-\mathrm{i}c(t)\sum_j y_j^3/6`$, where $`|c(t)|=O(\mu/d)`$ and $`|\mathrm{Im}\,c(t)|=O(\mu|t|/d)`$. Its real part is therefore $`O((\mu/d)|t|\sum_j|y_j|^3)`$, and the log expansion's quartic remainder is $`O((\mu/d)\sum_j y_j^4)`$. The central characteristic expansion gives $`(\log|\mathbb E e^{itS}|)''=-V+O(\mu |t|)\le-c\mu`$ in a sufficiently small fixed arc, by the centered moments just established. These are precisely the bounds used for the one-dimensional convolution majorant and the complex Gaussian approximation on the centered hyperplane. The convolution bound makes the sum of nonprincipal clusters relative to one saddle at most

$$
C\exp(C d^2/(n\mu))\sum_{j\ge1}\exp[-c(n\mu/d^2)((2j+1)^2-1)]=o(1).
$$

The relative error on either principal cube is $`O(d/\sqrt{n\mu}+d^2/(n\mu))`$ by the integrated Wick estimate for the centered Gaussian; there $`d\phi^2=O(1/d)`$. Choose the singleton zero arc $`|\theta_j|\le\eta`$ inside the small-phase range of the convolution estimate, reducing the fixed $`\eta`$ if necessary. Any lifted cluster has common phase in $`[-\eta,\eta]`$ and centered coordinates of magnitude at most $`2\eta`$. At either principal phase $`\pm\pi/d`$, the fixed centered cube of radius $`\eta/2`$ lies within the original zero arc for all sufficiently large $`d`$. The corresponding principal region therefore lies between cubes of radii $`\eta/2`$ and $`2\eta`$ in the centered hyperplane. The flagged-coordinate convolution estimate controls its part outside the smaller cube. Thus all constants in the two cited estimates are uniform here even for an unbounded cap. [Convolution estimate and cluster coordinates](https://github.com/ProgramComputer/open-math-research/blob/f7e10f84dd21fec44ca58c60bae0879d12ebd89b/topics/balanced-arrays/fixed-cap/fixed-cap-moving-u-localization.md) · [Integrated local Gaussian estimate](https://github.com/ProgramComputer/open-math-research/blob/f7e10f84dd21fec44ca58c60bae0879d12ebd89b/topics/balanced-arrays/fixed-cap/tall-sparse-transverse-saddle.md)

## Coefficients at $`k/d\to c\in(0,\infty)`$

Suppose now $`n/d^4\to\infty`$. In the unrestricted column model, choose independently for each column a uniform $`i`$-subset of the $`n`$ rows. The expected number of unordered pairs of occupied cells sharing a row is $`\binom d2 i^2/n`$. For $`i=k+O(1)`$ this is $`O(d^4/n)=o(1)`$. If no pair occurs, the cap is satisfied for every $`r\ge1`$. Therefore

$$
a_i=\binom ni^d(1+o(1))
$$

uniformly on every fixed window. Thus, with $`\Gamma_i=a_i^2/(a_{i-1}a_{i+1})`$ and $`t_i=\sqrt{a_{i-1}/a_{i+1}}`$, we have $`\log\Gamma_{k+j}\to1/c`$ for each fixed integer $`j`$. Also

$$
\log t_k=d\log\frac{k}{n-k}+\frac d2\log(1+1/k)-\frac d2\log(1+1/(n-k))+o(1).
$$

At the scalar tilt $`w_k`$ prescribed by $`\mathbb E S=dk/n`$, the small-mean series gives $`dw_k=\mu+O(\mu^2)`$. Hence $`d\log(w_k/(k/(n-k)))=O(d\mu+dk/n)=o(1)`$. We obtain $`\log t_k=d\log w_k+d/(2k)+o(1)`$ for these quotas. For $`k/d\to0`$ the orientation inequality gives $`\Gamma_k\ge(1+1/k)^d\to\infty`$ directly.
