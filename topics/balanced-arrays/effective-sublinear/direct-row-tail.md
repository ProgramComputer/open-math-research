# Direct row-conditioned Fourier tails at logarithmic aspect

Let $`u=\log n\ge10^6`$ and $`s=d/n\in[100/u,1]`$. Put $`\delta=\min(s,1/4)`$ and $`T=100/\delta`$, so $`400\le T\le u`$.
Suppose $`x=k/n\in[s/3,1-s/3]`$ and the integer row sizes $`\ell_i`$
satisfy $`\sum_i\ell_i=dk`$ and $`|p_i-x|\le n^{-1/4}`$ for $`p_i=\ell_i/d`$.
In each row independently choose a uniform $`\ell_i`$-subset. Write
$`\chi_i`$ for that row's vector characteristic function and put
$`v_i=p_i(1-p_i)`$, $`A=\sum_i v_i`$, and $`\Lambda=dA/(d-1)`$.
Use normalized Haar measure, and let $`E_\epsilon`$ be the event that
some pair of column angles has circular distance greater than
$`\epsilon=n^{-2/5}`$. Then

$$
\int_{E_\epsilon}\left|\prod_i\chi_i(\boldsymbol\theta)\right|d\theta
\le \sqrt d(2\pi\Lambda)^{-(d-1)/2} e^{T^2/12+1/2}
\left[
e^{-n^2/(4T^2)}
+n^{3/2}e^{3T^2-n^{1/5}/(40T^2)}
\right].
$$

In particular this is less than
$`e^{-T^2}n^{-10}\sqrt d(2\pi\Lambda)^{-(d-1)/2}`$.
The column-centering factor in the Fourier inversion for balance
is a pure phase and leaves the estimate unchanged.

## Passing from conditioned subsets to the row-angle envelope

Denote the Bernoulli mean atom by
$`b_i=\Pr(\mathrm{Bin}(d,p_i)=\ell_i)`$. Row Fourier inversion gives exactly

$$
b_i\chi_i(\boldsymbol\theta)=\int_{-\pi}^{\pi}
e^{-i\ell_i\phi}
\prod_{j=1}^d [1-p_i+p_i e^{i(\phi+\theta_j)}]
\frac{d\phi}{2\pi}.
$$

The normalized law given that row sum is the uniform row-subset
law. The elementary bound
$`|1-p+p e^{it}|\le e^{-p(1-p)(1-\cos t)}`$ follows by squaring
and using $`1-y\le e^{-y}`$. Apply it in each row integral and put
$`R=|\sum_j e^{i\theta_j}|`$. The row-angle integral of the envelope
is $`e^{-dv_i}I_0(v_i R)`$, where
$`I_0(z)=\int e^{z\cos t}\,dt/(2\pi)`$. Hence

$$
\left|\prod_i\chi_i(\boldsymbol\theta)\right|
\le\frac{B(R)}{\prod_i b_i},\qquad
B(R)=e^{-A(d-R)}\prod_i J(v_iR),\qquad J(z)=e^{-z}I_0(z).
$$

Thus the joint-envelope argument bounds the directly conditioned
row integral. Absolute values are taken inside each row integral,
so no estimate of the phases of those individual integrals is used.
Both the modulus and $`E_\epsilon`$ are invariant under a common
column-angle translation. It follows that the same integrals are
obtained on the section $`\theta_d=0`$.

## Determinant-scale bound on the envelope tail

Set $`B_0=\prod_i(2\pi d v_i)^{-1/2}`$ and
$`G=\sqrt d(2\pi A)^{-(d-1)/2}B_0`$.
The interval for $`x`$ and $`n^{-1/4}\le\delta/12`$ give
$`p_i\in[\delta/4,1-\delta/4]`$ and $`v_i\ge1/T`$, with $`A\ge n/T`$.
Also $`d\ge n/T`$. The one-dimensional bounds used below are

$$
J(z)\ge(6\sqrt{1+z})^{-1}\quad(z\ge0),\qquad
J(z)\le e^{1/(2z)}(2\pi z)^{-1/2}\quad(z\ge10).
$$

These follow directly from the cosine integral as in the
[existing Bessel proof](https://github.com/ProgramComputer/open-math-research/blob/7b585bad34491cf9e733a316e1b62f6c3529880f/topics/balanced-arrays/bessel-margins/upper.md).

On $`R<d/2`$, use $`J\le1`$ to get $`B(R)\le e^{-n^2/(2T^2)}`$.
Every variance factor is at most $`n`$, so $`G\ge(2\pi n)^{-n}`$.
Since $`\log(2\pi n)< n/(4T^2)`$, the relative diffuse-region
loss is at most $`e^{-n^2/(4T^2)}`$.

On $`R\ge d/2`$, the Bessel arguments satisfy $`v_iR\ge n/(2T^2)\ge10`$.
Their total exponential cost is at most
$`\sum_i(2v_iR)^{-1}\le Tn/d\le T^2`$.
The factors $`(d/R)^{1/2}`$ multiply to at most
$`\exp[n(d-R)/d]`$. Thus for $`A'=A-n/d\ge n/(2T)`$,

$$
B(R)\le e^{T^2}B_0 e^{-A'(d-R)}.
$$

The lower bound on $`J`$ converts $`e^{A'R}`$ to
$`6\sqrt{1+A'd}\,I_0(A'R)`$. The defining integral for the last term is

$$
I_0(A'R)=\int_{-\pi}^{\pi}\prod_j e^{A'\cos(\theta_j-\beta)}
\frac{d\beta}{2\pi}.
$$

For fixed $`\beta`$ the factors normalize to independent von Mises
angles with common parameter $`A'`$. Their product normalization is
$`I_0(A')^d`$. Applying the upper Bessel bound at $`A'`$ and dividing by
$`G`$ gives at most $`e^{2T^2}`$ times the probability of the column event
in that product law. To check the constant, the extra exponent from
$`I_0(A')^d`$ is at most $`d/(2A')\le T`$. Replacing the determinant's $`A'`$
by $`A`$ costs at most $`n/(2A')\le T`$ in the exponent. The remaining
factor is $`6\sqrt{(1+A'd)/(2\pi A'd)}\le6`$.

If $`E_\epsilon`$ holds, for any $`\beta`$ at least one column angle
has circular distance greater than $`\epsilon/2`$ from $`\beta`$.
The von Mises tail at distance $`t`$ with parameter $`z`$ is at most
$`6\sqrt{1+z}\,e^{-zt^2/5}`$, using $`1-\cos t\ge t^2/5`$ up to $`\pi`$
and the lower bound on $`J`$. Thus the product-law probability
is at most $`6d\sqrt{1+A'}\exp[-A'\epsilon^2/20]`$.
Since $`A'\le A\le n/4`$, this bound is at most
$`6n^{3/2}\exp[-n^{1/5}/(40T)]`$. Combining the two regions gives

$$
\int_{E_\epsilon} B(R)\thinspace{}d\theta
\le G\left[e^{-n^2/(4T^2)}
+n^{3/2}e^{3T^2-n^{1/5}/(40T^2)}\right]
$$

with room in the weakened aligned-region exponent.

## Normalization at the true subset covariance

The exact covariance of a single uniform-size row on the
sum-zero column subspace is $`d v_i/(d-1)`$ times the identity.
Indeed the diagonal variances are $`v_i`$, the off-diagonal
covariances are $`-v_i/(d-1)`$, and the common-angle direction
has variance zero. Their sum gives precision $`\Lambda=dA/(d-1)`$
for the Gaussian exponent on that subspace.
In the gauge with one column angle fixed, its matrix is
$`\Lambda(I_{d-1}-\mathbf1\mathbf1^{\mathsf T}/d)`$, whose determinant
is $`\Lambda^{d-1}/d`$.

Stirling's lower bound for each row mean atom gives
$`b_i\ge(2\pi d v_i)^{-1/2}e^{-1/(12d v_i)}`$.
Here all $`p_i`$ are interior. Hence $`B_0/(\prod_i b_i)\le e^{T^2/12}`$.
Changing the Gaussian factor from $`A`$ to $`\Lambda`$ costs only

$$
\left(\frac{\Lambda}{A}\right)^{(d-1)/2}
=\left(1+\frac1{d-1}\right)^{(d-1)/2}<e^{1/2}.
$$

Together these yield the claimed tail in subset Gaussian units.

For explicit numerical controls, $`n^{1/4}\ge u/4\ge12/\delta`$ ensures
regular variances. Also $`n\ge u^4/24`$ gives $`n\ge20T^2`$ and
$`\log(2\pi n)<2u<n/(4T^2)`$, using $`T\le u`$ and $`u\ge10^6`$.
Use the sixth Taylor term for the aligned-region exponent:

$$
\frac{n^{1/5}}{40T^2}
\ge\frac{u^6}{450{,}000{,}000T^2}
\ge\frac{u^4}{450{,}000{,}000}>1000u^2.
$$

The diffuse exponent is also larger than $`1000u^2`$, since
$`n^2/(4T^2)\ge u^6/2304`$. The prefactor $`e^{T^2/12+1/2}`$,
the aligned loss $`3T^2+(3/2)u`$, and the extra factor of two from
adding the regions are absorbed by this margin. In detail
$`(4+1/12)T^2+(23/2)u+1/2+\log2<1000u^2`$ for $`u\ge10^6`$,
so the sum is less than $`e^{-T^2-10u}`$. This verification uses
only $`d\ge100n/\log n`$ and $`u\ge10^6`$.
