# A uniform upper bound for column balance at a fixed row profile

Let $n\ge1000$, $n/4\le d\le n$, and let the uniform cap be $r\le d$. Fix a
row profile of integers $0\le \ell_i\le r$ with $\sum_i\ell_i=dk$.
Independently in each row choose a uniform $\ell_i$-subset of the $d$
columns. Let $P_{\ell}$ be the probability that all column sums equal $k$.
Write $x=k/n$, $e=nr-dk$, and $B=\sum_i((r-\ell_i)/d)^2$. If $1/5\le x\le4/5$ and $0\le e\le nd/100$,
then

$$
P_{\ell}\le
\exp(72+\min(9e/d,58B))\sqrt{nd}\,[2\pi n x(1-x)]^{-d/2}.
$$

In particular, the estimate holds on the requested interval $0.295n\le d\le n$.
The prefactor is uniform over row profiles, including those containing rows
of size zero or $d$. The condition $e\le nd/100$ is the explicit relative
near-saturation condition $r/d-x\le 1/100$.

## Joint Fourier bound and exact row-angle integration

Put $p_i=\ell_i/d$, $v_i=p_i(1-p_i)$, and let
$b_i=\Pr(\mathrm{Bin}(d,p_i)=\ell_i)$. Introduce independent Bernoulli cells
with parameter $p_i$ in row $i$. Conditioning on all row sums equal to
their prescribed values gives exactly the independent uniform row subsets
above, and the probability of this conditioning event is $\prod_i b_i$.
This holds for $p_i=0$ and $p_i=1$ as deterministic cases.

Fourier inversion for the joint row and column margin event allows
redundant coordinates, because it is an orthogonality identity for each
integer coordinate. Take absolute values before integrating and use

$$
|1-p+p e^{it}|^2=1-2p(1-p)(1-\cos t)
\le \exp[-2p(1-p)(1-\cos t)].
$$

Write $R=|\sum_{j=1}^d e^{i\theta_j}|$, where $\theta_j$ is the $j$th
column angle. For each row, integration in its angle $\phi_i$ now gives
$e^{-dv_i} I_0(v_iR)$, where
$I_0(z)=(2\pi)^{-1}\int_{-\pi}^{\pi} e^{z\cos t}\,dt$.
With normalized Haar integration in the column angles this proves

$$
P_{\ell}\le\int\prod_{i=1}^n
\frac{e^{-dv_i}I_0(v_iR)}{b_i}\,d\theta.
$$

## Uniform Bessel and binomial bounds

Set $J(z)=e^{-z}I_0(z)$ for $z\ge0$. The following estimates suffice:

$$
\frac1{6\sqrt{1+z}}\le J(z)\le\frac{5}{4\sqrt{1+z}}
\quad(z\ge0),\qquad
J(z)\le\frac{e^{1/(2z)}}{\sqrt{2\pi z}}\quad (z\ge10).
$$

For the lower bound, restrict the angle integral on $[0,\pi]$ to
$[0,(1+z)^{-1/2}]$ and use $1-\cos t\le t^2/2$. For the first upper bound,
$1-\cos t\ge2t^2/\pi^2$ on $[0,\pi]$, which gives
$J(z)\le\min(1,\sqrt\pi/(2\sqrt{2z}))$ for $z>0$.
The maximum of $\sqrt{1+z}\min(1,(2/3)/\sqrt z)$ occurs at $z=4/9$
and is less than $5/4$. For the sharper upper bound put
$u=2\sin(t/2)$, so the kernel becomes $e^{-zu^2/2}$ and the Jacobian is
$(1-u^2/4)^{-1/2}$. On $0\le u\le\sqrt2$, this Jacobian is at most
$1+3u^2/8$, by bounding its derivative in $u^2$. The rest of the angle
integral contributes at most $e^{-z}$. The resulting bound is

$$
J(z)\le (2\pi z)^{-1/2}(1+3/(8z))+e^{-z}.
$$

For $z\ge10$, $\sqrt{2\pi}z^{3/2}e^{-z}<1/8$ by monotonicity and evaluation
at $10$. This proves the claimed sharper estimate.

For $1\le\ell_i\le d-1$, the elementary two-sided Stirling inequality for
factorials gives

$$
b_i\ge (2\pi d v_i)^{-1/2}\exp[-1/(12dv_i)].
$$

Indeed the denominator errors are bounded by
$1/(12\ell_i)+1/(12(d-\ell_i))=1/(12dv_i)$.
Since $dv_i\ge1/2$ and $v_i\le1/4$, this also gives
$b_i\ge (3\sqrt d)^{-1}$. At a deterministic row $b_i=J(v_iR)=1$.

## The region of aligned column angles

Write $A=\sum_i v_i$ and $A_0=nx(1-x)$. Since $\sum_i p_i=nx$ and
$p_i\le x+e/(nd)$,

$$
A_0-A=\sum_i(p_i-x)^2=B-\frac{e^2}{nd^2}\le\min(x e/d,B).
$$

The inequality by $xe/d$ follows by summing $p_i^2\le (x+e/(nd))p_i$. The identity for $B$ follows by centering the squared deficits at their mean $e/(nd)$.
Thus $A\ge 3n/20$ under the stated assumptions.

Call a row good if $1/10\le p_i\le9/10$. There are no rows above $9/10$,
since $p_i\le81/100$. The number $m$ of other rows is at most $10e/d$:
each has $x-p_i\ge1/10$, whereas the sum of all positive deficits
$(x-p_i)_+$ is the sum of all positive excesses $(p_i-x)_+$ and is at
most $n(e/(nd))=e/d$. Each such row also has $r/d-p_i\ge1/10$, so $m\le100B$.

On $R\ge d/2$, a good row has $v_i\ge9/100$ and $v_iR\ge10$.
Its factor in the integral is at most

$$
e^{-v_i(d-R)}(d/R)^{1/2}
\exp\left[\frac1{12dv_i}+\frac1{2v_iR}\right].
$$

The product of the last exponentials is at most $e^{49}$, since their
exponents sum to at most $(13/12)(100/9)n/d<49$.
For every other nondeterministic row the cosine bound above gives
$J(z)\le(\pi/2)(2\pi z)^{-1/2}$ for $z>0$. Its factor is therefore at most

$$
e^{-v_i(d-R)}(d/R)^{1/2}(\pi/2)e^{1/(12dv_i)}
\le e^{-v_i(d-R)}(d/R)^{1/2}e^{27/50}.
$$

Here $dv_i\ge249/250$ since $d\ge250$, and
$\log(\pi/2)+250/(12\cdot249)<27/50$.
For example, use $\pi<22/7$ and the exponential Taylor sum through degree
three to check the strict comparison. Deterministic rows contribute one,
which satisfies the same bound. Hence the sparse rows cost at most
$\exp[\min(27e/(5d),54B)]$ beyond their shared exponential and square-root
factors.

On this region, $\frac12\log(d/R)\le(d-R)/d$.
Set $A'=A-n/d$. The entire product of row factors on $R\ge d/2$
is therefore at most

$$
\exp(49+\min(27e/(5d),54B)-A'(d-R)).
$$

Here $A'\ge (7/50)n$ and $A'\le n/4$, using $n\ge1000$ and $n/d\le4$.
By the uniform lower Bessel bound,
$e^{A'R}\le 6\sqrt{1+A'd}\,I_0(A'R)$.
Introducing one extra common angle under the integral of $I_0(A'R)$
and then integrating each column angle shows exactly that

$$
\int I_0(A'R)\,d\theta=I_0(A')^d.
$$

Since $A'\ge10$, the integral of $\exp[-A'(d-R)]$ over the full torus
is consequently bounded by
$6\sqrt{1+A'd}\,(2\pi A')^{-d/2}\exp[d/(2A')]$.
Here $1+A'd\le nd$, $d/(2A')<4$, and

$$
\frac d2\log(A_0/A')
\le\frac{d}{2A'}(\min(x e/d,B)+n/d)
\le 15+\min(3e/d,4B).
$$

The contribution from $R\ge d/2$ is therefore at most
$\exp(70+\min(9e/d,58B))\sqrt{nd}(2\pi A_0)^{-d/2}$.

## The remaining torus region

On $R<d/2$ use $J\le1$ and $b_i\ge(3\sqrt d)^{-1}$ for each row.
The contribution is at most $(3\sqrt d)^n e^{-Ad/2}$.
Since $A\ge3n/20$ and $d\ge n/4$, this is at most $(2n)^{-d/2}$:
after taking logarithms and dividing by $n$, it suffices that

$$
\log 3+\tfrac12\log n+\tfrac12\log(2n) < 3n/160 .
$$

The left hand side is less than $\log(5n)$, and the displayed comparison
holds at $1000$ and improves thereafter. Finally $2\pi A_0<2n$,
so $(2n)^{-d/2}\le\sqrt{nd}(2\pi A_0)^{-d/2}$.
Adding the two region bounds proves the theorem, with room in the constant
$72$.

## Consequence for scalar deficit coefficients

Write $Q(t)=\sum_{j=0}^r \binom d{r-j} t^j$.  The number of row-constrained
arrays with total deficit $e$ before imposing column balance is
$[t^e]Q(t)^n$. Weight each row profile by the product of the numbers of
allowed choices in its rows and normalize by this coefficient. Write
$\mathbb E_e$ for expectation under that profile law, and
$B=\sum_i((r-\ell_i)/d)^2$ for the random squared-deficit sum. Conditional
on the profile, the column-balance probability is exactly the one bounded
above. Hence

$$
a(n,k,r,d)\le [t^e]Q(t)^n\,
e^{72}\mathbb E_e\!\left[e^{\min(9e/d,58B)}\right]
\sqrt{nd}\,[2\pi n x(1-x)]^{-d/2}.
$$

In particular, the expectation can be replaced by the uniform factor
$e^{9e/d}$.

The estimate is one-sided. A curvature lower bound still requires a
matching lower bound for the balanced coefficient in the numerator, or
another comparison across adjacent quotas.
