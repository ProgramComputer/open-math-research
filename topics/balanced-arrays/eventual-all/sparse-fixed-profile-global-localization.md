# Global localization for sparse fixed-profile equal-column conditioning

Let $`d\to\infty`$. For each row with prescribed size $`s`$ choose a uniform $`s`$-subset of the $`d`$ columns, independently across rows. Rows of size zero may be omitted. Suppose that the total size is $`M=dk`$, with $`k/d\to\beta\in(0,\infty)`$, and the maximal row size $`s_{\max}=o(d)`$. Write

$$
f_s(\vec z)=\frac{e_s(\vec z)}{\binom ds},\qquad
\Lambda=\sum_{\rm rows}\frac{s(d-s)}{d(d-1)}
=k(1+o(1)),\qquad
G_d=\sqrt d\thinspace (2\pi\Lambda)^{-(d-1)/2}.
$$

Here each $`z_i`$ lies on the unit circle. For any fixed $`\eta>0`$, there is a fixed $`L`$ depending on $`\beta`$ such that the absolute contribution of the following two regions to the balanced-column integral is $`o(G_d)`$:

- $`D_z=\sum_i|z_i-\overline z|^2>L`$, where $`\overline z=d^{-1}\sum_i z_i`$.
- $`D_z\le L`$ and some $`z_i`$ is at angular distance at least $`\eta`$ from $`\overline z/|\overline z|`$.

The estimates are exponential relative to $`G_d`$ for fixed $`\eta`$ and fixed $`\beta`$. Thus the remaining quotient chart has bounded centered sum of squared angles and arbitrarily small fixed maximum angle deviation. More generally one may take $`\eta=\eta_d\downarrow0`$ as long as $`\eta_d^2\gg (s_{\max}/d)^2+(\log d)/d`$, using the refinement at the end.

The character integral on the full torus with product Haar measure is

$$
\Pr(\text{column sums all }k)
=\int \left(\prod_i z_i^{-k}\right)\prod_{\rm rows} f_s(\vec z)\thinspace d\vec z.
$$

The integrand is invariant under simultaneous rotation because $`M=dk`$. In particular estimates on the full torus apply directly to its quotient integral. In the local zero-sum angular hyperplane, the projection of the chart with last angle fixed has Gram determinant $`1/d`$, so the normalized Gaussian measure of precision $`\Lambda`$ is $`G_d`$. The bounds below are absolute and therefore independent of the choice of character.

## A uniformly exponential bound for each row

Write $`D=D_z=d(1-|\overline z|^2)`$. For every $`1\le s\le d/2`$,

$$
|f_s(\vec z)|\le \exp(-c sD/d).
\tag{1}
$$

First use the Cauchy coefficient circle of radius $`r=s/(d-s)`$ in $`\prod_i(1+v z_i)`$. Put $`p=s/d`$. Since $`|1+r e^{i\theta}|/(1+r)\le \exp[-p(1-p)(1-\cos\theta)]`$,

$$
|f_s(\vec z)|
\le
\frac{(1+r)^d}{r^s\binom ds}
\thinspace e^{-p(1-p)d(1-|\overline z|)}
\int_{-\pi}^{\pi}e^{-p(1-p)d|\overline z|(1-\cos\theta)}
\thinspace \frac{d\theta}{2\pi}.
$$

The prefactor is the inverse mass of $`\mathrm{Bin}(d,p)`$ at its mean and is at most $`C\sqrt s`$ by Stirling. The integral is at most $`C/\sqrt{1+s|\overline z|}`$ by $`1-\cos\theta\ge c\theta^2`$ on this interval and $`1-p\ge1/2`$. If $`|\overline z|\ge1/2`$, the combined prefactor is bounded, and $`1-|\overline z|\ge D/(2d)`$. If $`|\overline z|<1/2`$, the exponent gives $`e^{-cs}`$, which absorbs $`\sqrt s`$ with a reduction of $`c`$. In both cases this proves $`|f_s|\le C e^{-c sD/d}`$.

To remove that constant when $`sD/d`$ is bounded, generate a uniform size-$`s`$ subset by taking $`s`$ disjoint random pairs from a uniform permutation and independently choosing one element of each pair. Given the pairs, the Fourier response has modulus at most $`e^{-X/8}`$, where $`X`$ is their sum of squared chords. A uniform pair has expected squared chord $`2D/(d-1)`$, so $`\mathbb EX=2sD/(d-1)`$. Each chord squared is at most four. For two disjoint pairs the product expectation is at most $`d(d-1)/[(d-2)(d-3)]`$ times the squared single-pair mean, by dropping the disjointness restriction in the numerator. Thus $`\mathbb E X^2\le C(\mathbb EX+(\mathbb EX)^2)`$. By $`1-e^{-x/8}\ge c x/(1+x)`$ and Cauchy–Schwarz,

$$
1-|f_s|\ge c\thinspace \mathbb E\frac{X}{1+X}
\ge c\thinspace \frac{(\mathbb EX)^2}{\mathbb E(X+X^2)}
\ge c'\min(sD/d,1).
$$

The zero-mean case is immediate. For $`sD/d`$ above a fixed large constant use the Cauchy estimate and absorb its prefactor. Below that constant use this last lower bound on the loss, with another absolute constant. This proves (1), and hence $`|\prod f_s|\le e^{-c kD}`$ globally. It uses no restriction on the degree product beyond the eventual $`s_{\max}\le d/2`$.

## Large dispersion

Let

$$
B_{\vec z}(\tau)=\sum_i|z_i-e^{i\tau}|^2,\qquad
\min_\tau B_{\vec z}(\tau)=2d(1-|\overline z|).
$$

Thus $`D\ge\tfrac12\min_\tau B_{\vec z}(\tau)`$. On $`D>L`$ reserve half of the bound $`e^{-c kD}`$ for a factor $`e^{-c' kL}`$. For the remaining half, approximate the minimizing common phase by its nearest point on a uniform circle grid of $`d`$ angles. The squared-chord sum increases by at most $`C/d`$, because its increase is $`2d|\overline z|(1-\cos\Delta)`$ with $`|\Delta|\le\pi/d`$. This also holds by choosing any common phase when $`\overline z=0`$. Since $`k=O(d)`$, discretization changes the remaining bound by only a bounded factor. At each grid point the resulting product of one-coordinate chord factors integrates to at most $`(C/\sqrt k)^d`$ by independence. Union over the grid gives

$$
\int_{D>L}\left|\prod f_s\right|\le C d\thinspace  e^{-c'kL}(C/\sqrt k)^d.
$$

The ratio to $`G_d`$ is $`\exp[-c'kL+O(d)]`$, using $`\Lambda/k\to1`$ and $`k/d\to\beta`$. Choosing $`L`$ sufficiently large makes this exponentially small in $`d`$.

## Bounded dispersion and an exceptional coordinate

Fix this $`L`$ and suppose $`D\le L`$. For large $`d`$ the mean is nonzero and close to unit modulus. Write $`u_i=z_i/\overline z-1`$, so $`\sum_i u_i=0`$, $`\sum_i|u_i|^2=O(L)`$, and $`\max_i|u_i|\le3`$. The exact subset expansion is

$$
f_s=\overline z^{\thinspace s}\sum_{j=0}^s\frac{(s)_j}{(d)_j}e_j(\vec u).
$$

To bound its coefficients, take a fixed circle $`|v|=1/8`$ in $`\prod_i(1+v u_i)`$. The logarithm has no linear term and satisfies

$$
\left|\sum_i \log(1+v u_i)\right|
\le C |v|^2\sum_i|u_i|^2\le C_L.
$$

Cauchy's coefficient bound gives $`|e_j|\le C_L8^j`$, and $`e_1=0`$. Since $`(s)_j/(d)_j\le(s/d)^j`$ and $`s_{\max}/d=o(1)`$, the sum of the terms with $`j\ge2`$ is $`O_L((s/d)^2)`$. Multiplication over rows gives

$$
\left|\prod f_s\right|
\le |\overline z|^{dk}\exp[O_L(k s_{\max}/d)]
\le \exp[-kD/2+O_L(k s_{\max}/d)].
\tag{2}
$$

The overhead in (2) is $`e^{o(d)}`$. The coefficient $`1/2`$ in its quadratic loss is needed for the exceptional-coordinate argument.

For $`D\le L`$, the relation to the optimal chord sum sharpens to $`D\ge(1-C_L/d)\min_\tau B_{\vec z}(\tau)`$. Set $`A=(k/2)(1-C_L/d)`$ and again discretize the minimizing phase on the $`d`$-point grid. The increase in $`B_{\vec z}`$ costs a bounded factor in (2). If some coordinate is at circular distance $`\eta`$ or more from the minimizing phase, it remains at distance at least $`\eta/2`$ from the nearest grid point for sufficiently large $`d`$.

A single unflagged coordinate has the integral

$$
J(A)=\int_{-\pi}^{\pi}e^{-A|e^{i\theta}-1|^2}\thinspace \frac{d\theta}{2\pi}
=\frac{1+O(A^{-1})}{\sqrt{4\pi A}}.
$$

Indeed the chord square differs from $`\theta^2`$ by $`O(\theta^4)`$ and is at least $`c\theta^2`$. Bounding the difference of exponentials by $`C A\theta^4e^{-cA\theta^2}`$ gives the stated relative error. At a flagged coordinate with $`|\theta|\ge\eta/2`$, keep half its exponent to gain $`e^{-cA\eta^2}`$ and integrate the rest. This yields at most $`C J(A)e^{-c'A\eta^2}`$ for that coordinate. Union over the possible flags and grid points proves

$$
\int_{\lbrace D\le L,\ \mathrm{exception}\rbrace}\left|\prod f_s\right|
\le C d^2 e^{O_L(k s_{\max}/d)} J(A)^d e^{-c' A\eta^2}.
$$

Since $`4\pi A=2\pi k(1-O_L(1/d))`$, the ratio $`J(A)^d/G_d`$ is at most $`\exp(O_L(1)+O(|\log(dk)|)+O(k s_{\max}/d))`$. Here one may also use the simpler bound $`e^{o(d)}`$ for fixed $`\eta`$. This proves the exceptional-coordinate estimate for fixed cutoff, or for a shrinking cutoff whose squared size dominates $`s_{\max}/d+(\log d)/d`$.

In the retained region the angles relative to the mean direction are all smaller than $`\eta`$ and have squared sum $`O(L)`$ by the chord bound. Subtracting their arithmetic mean gives a zero-sum angle chart with maximum deviation at most $`2\eta`$ and squared sum still $`O(L)`$. For small fixed $`\eta`$ this chart is injective modulo a common rotation, because pairwise angle differences uniquely determine its small zero-sum lift. The local cumulant expansion and its correction constant concern this retained chart and are separate from the absolute estimates established here.


## A sharper shrinking cutoff

Retaining the degree-two term in the centered elementary-symmetric expansion improves the overhead. Since $`e_2(\vec u)=-\frac12\sum_i u_i^2`$,

$$
\mathrm{Re}\thinspace e_2(\vec u)
=\frac12\sum_i |u_i|^2-\sum_i(\mathrm{Re}\thinspace u_i)^2
\le \frac{D}{2|\overline z|^2}.
$$

The terms of degree at least three have sum $`O_L((s/d)^3)`$ by the same Cauchy estimates. The logarithm of the modulus of the centered factor therefore has upper bound
$`[(s)_2/(d)_2]D/(2|\overline z|^2)+O_L((s/d)^3)`$, with its quadratic logarithm error absorbed there. Use
$`s/d-(s)_2/(d)_2=s(d-s)/(d(d-1))`$ and $`|\overline z|^{-2}=1+O_L(1/d)`$. Summing over rows gives

$$
\log\left|\prod f_s\right|
\le-\Lambda D/2 + O_L\bigl(1+k(s_{\max}/d)^2\bigr).
$$

Thus in the grid proof one can use $`A=(\Lambda/2)(1-O_L(1/d))`$. The exceptional-coordinate loss then dominates its overhead and the polynomial unions whenever $`\eta_d^2\gg (s_{\max}/d)^2+(\log d)/d`$.
