# Uniform local limit for balance at fixed row sizes

Fix $`r\ge1`$. Let $`d\to\infty`$, take any finite list $`s_1,\ldots,s_n\in\{0,\ldots,r\}`$, and let $`X_i`$ be independent indicators of uniform $`s_i`$-subsets of $`[d]`$. Write $`M=\sum_i s_i=dk`$ for an integer $`k`$, and assume $`M/d^2\to\infty`$. Then, uniformly over those lists,

$$
\mathbb P\negthinspace \left(\sum_i X_i=k\mathbf 1\right)
=\sqrt d\thinspace (2\pi\Lambda)^{-(d-1)/2}(1+o(1)),
\qquad
\Lambda=\sum_i\frac{s_i(d-s_i)}{d(d-1)}.
$$

In particular $`\Lambda\asymp M/d`$. The local relative error is $`O(d/\sqrt M+d^2/M)`$ and the global relative tail is at most $`d^2 C^d\exp(-c M/d)`$, where constants depend only on the fixed cap.

## Quotient and normalization

Let $`f_s(\theta)=\mathbb E\exp(i\sum_{j\in S}\theta_j)`$ for a uniform $`s`$-subset $`S`$. Pinned-coordinate Fourier inversion in angles $`\theta_1,\ldots,\theta_{d-1}`$ with $`\theta_d=0`$ gives the probability as the normalized integral of $`\prod_i f_{s_i}(\theta)\exp(-ik\sum_j\theta_j)`$. The integrand is invariant under common phase shifts because $`M=dk`$. It is also periodic in each coordinate because $`k`$ is an integer.

Project orthogonally onto $`V=\mathbf 1^\perp`$ by $`P=I-\mathbf 1\mathbf 1^\top/d`$. The period lattice in $`V`$ has basis $`2\pi Pe_1,\ldots,2\pi Pe_{d-1}`$, as $`Pe_d=-\sum_{j<d}Pe_j`$. Their Gram determinant after removal of the $`2\pi`$ factors is $`\det(I_{d-1}-\mathbf 1\mathbf 1^\top/d)=1/d`$. The covolume of the projected pinned-coordinate cube is therefore $`(2\pi)^{d-1}/\sqrt d`$.

For any sufficiently small fixed $`\eta>0`$, the image of the cube $`C_\eta=\{y\in V:\max_j|y_j|\le\eta\}`$ is injective into the quotient. Indeed any period difference has pairwise coordinate differences that are integer multiples of $`2\pi`$, impossible for a nonzero period vector in $`C_\eta-C_\eta`$ if $`4\eta<2\pi`$. On this cube the centered integrand is $`\prod_i f_{s_i}(y)`$.

## Uniform local expansion

For $`y\in V`$, put $`L=\sum_{j\in S}y_j`$. The inclusion probabilities are $`h_j=(s)_j/(d)_j`$. Its first moment vanishes, and direct expansion gives

$$
\mathbb E L^2=(h_1-h_2)\sum_j y_j^2,\qquad
\mathbb E L^3=(h_1-3h_2+2h_3)\sum_j y_j^3.
$$

Here $`\sum_{a\ne b}y_a^2y_b=-\sum_a y_a^3`$ and the ordered distinct triple sum is $`2\sum_a y_a^3`$. The absolute fourth moment is at most $`r^3(s/d)\sum_j y_j^4`$ by the convexity inequality for a sum of $`s`$ terms. Choosing a fixed small cube makes $`|f_s(y)-1|\le C(s/d)\sum_j y_j^2`$ small, and squaring this bound is $`O((s/d)\sum_j y_j^4)`$ by Cauchy–Schwarz and fixed $`r`$. Hence

$$
\sum_i\log f_{s_i}(y)=-\frac{\Lambda}2\sum_j y_j^2
-\frac{i}{6}\gamma\sum_j y_j^3+E(y),\qquad
|\gamma|\le CM/d,\quad |E(y)|\le C(M/d)\sum_j y_j^4.
$$

The constant $`\gamma`$ is real, and $`h_1-h_2=s(d-s)/[d(d-1)]`$. Zero sizes contribute nothing.

Let $`Y_j=Z_j-\overline Z`$ with independent $`Z_j\sim N(0,\Lambda^{-1})`$. This represents the Gaussian on $`V`$ with identity covariance on $`V`$ times $`\Lambda^{-1}`$. Put $`q_{ab}=\Lambda^{-1}(\delta_{ab}-1/d)`$. Wick gives $`\mathbb E Y_a^3Y_b^3=9q_{aa}q_{bb}q_{ab}+6q_{ab}^3`$. The first term cancels on summation since the diagonal entries agree and all row sums of $`q`$ vanish. Therefore $`\|\sum_jY_j^3\|_2=O(\sqrt d\,\Lambda^{-3/2})`$, and $`\|\sum_jY_j^4\|_2=O(d\Lambda^{-2})`$ by the eighth moment and triangle inequality. Writing $`B=-i\gamma\sum_jY_j^3/6+E(Y)`$ gives

$$
\Vert B\mathbf 1_{C_\eta}\Vert _2=O(d/\sqrt M+d^2/M).
$$

For exponential integrability, bound $`2(\mathrm{Re}B)_+`$ by $`C\Lambda\sum_jY_j^4`$ on $`C_\eta`$. The event $`|\overline Z|\le\eta`$ has probability tending to one and is independent of $`Y`$. With that event and $`Y\in C_\eta`$, one has $`|Z_j|\le2\eta`$ and $`\sum_jY_j^4\le16\sum_j Z_j^4`$. Thus the required truncated exponential expectation is bounded by a constant times
$`\bigl(\mathbb E[\mathbf 1_{|Z_1|\le2\eta}\exp(C'\Lambda Z_1^4)]\bigr)^d`$.
Choose $`\eta`$ small enough that $`C'\Lambda z^4\le\Lambda z^2/4`$ on the interval. Using $`e^t-1\le te^t`$ and the fourth Gaussian moment with doubled variance bounds each factor by $`1+O(1/\Lambda)`$. Their product is bounded since $`d/\Lambda=O(d^2/M)=o(1)`$. Cauchy–Schwarz applied to $`|e^B-1|\le|B|e^{(\mathrm{Re}B)_+}`$ gives the local relative error. The missing Gaussian mass outside $`C_\eta`$ is at most $`2d\exp(-c\eta^2\Lambda)`$. The full Gaussian integral is $`(2\pi/\Lambda)^{(d-1)/2}`$. Multiplying by the normalized quotient density yields the stated constant.

## Global localization by one-element exchange

Write $`z_j=e^{i\theta_j}`$, $`\bar z=d^{-1}\sum_jz_j`$, and $`V_z=\sum_j|z_j-\bar z|^2`$. For $`s\ge1`$, choose a uniform $`(s-1)`$-subset $`A`$ and then append $`j`$ uniformly from its complement of size $`q=d-s+1`$. This gives a uniform $`s`$-subset. By conditional Jensen, $`1-|f_s|^2`$ is at least the expected conditional variance of $`z_j`$. The variance on a fixed complement is the sum of ordered squared pair differences divided by $`2q^2`$. Averaging over the complement retains each pair with probability $`q(q-1)/(d(d-1))`$. Thus

$$
1-|f_s|^2\ge\frac{d(d-s)}{(d-1)(d-s+1)}\frac{V_z}{d}.
$$

For sufficiently large $`d`$ and fixed $`r`$, this is at least $`c_r(s/d)V_z`$. The zero-size case is trivial. Consequently $`|\prod_i f_{s_i}|\le e^{-c(M/d)V_z}`$.

Choose an anchor $`a`$ minimizing $`|z_a-\bar z|`$. Then $`\sum_j|z_j-z_a|^2=V_z+d|z_a-\bar z|^2\le2V_z`$. On the quotient choose principal anchor angles $`t_j=\arg(z_j/z_a)\in[-\pi,\pi]`$ for $`j\ne a`$. These coordinates have the normalized Haar product measure, as can also be seen by redoing the pinned-coordinate parametrization with $`a`$ fixed. Chord length satisfies $`|z_j-z_a|\ge 2|t_j|/\pi`$. If every $`|t_j|\le\eta/2`$, the projection of the anchor angle vector with $`t_a=0`$ belongs to $`C_\eta`$. Therefore outside the local image at least one anchor coordinate exceeds $`\eta/2`$. Partition by the choice of closest anchor, then bound the integral by a sum of $`d`$ unrestricted pinned-coordinate integrals with that tail event. A union bound over the $`d-1`$ coordinates and one-dimensional Gaussian bounds give

$$
\left|\int_{\mathrm{outside}}\prod_i f_{s_i}(\theta)e^{-ik\sum_j\theta_j}\thinspace d\mathrm{Haar}\right|
\le d^2 \left(\frac{C}{\sqrt{\Lambda}}\right)^{d-1}e^{-c\eta^2\Lambda}.
$$

Its ratio to the main Gaussian contribution is at most $`d^2 C_1^d e^{-c_1 M/d}=o(1)`$ because $`M/d^2\to\infty`$. This proof uses no distribution or tail hypothesis for the row sizes beyond the fixed cap.
