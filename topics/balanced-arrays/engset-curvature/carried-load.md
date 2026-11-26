# Convexity of the single-row saddle correction in carried load

For integers $1\le r<d$, let $G(z)=\sum_{j=0}^r\binom dj z^j$ with $z>0$. Let $S$ have probabilities proportional to these terms, $x=\mathbb E S/d$, $V=\mathrm{Var}(S)$, and $\rho=r/d$. Then $x$ strictly increases with $z$ from zero to $\rho$, since $dx/d\log z=V/d$. Define $g(x)=\log(z(1-x)/x)$.

**Result.** On $0<x<\rho$, $g'>0$ and

$$
g''\ \ge\ (g')^2+\frac{2g'}{1-x}>0.
$$

The first inequality is equality at $r=1$ and strict for $r\ge2$. As a consequence,

$$
d\,x\frac{\rho-x}{\rho}\ \le\ V\ <\ d\,x(1-x).
$$

The lower bound is equality at $r=1$ and strict for $r\ge2$. These are scalar statements about the tilted one-row law. The same variance bounds follow from the classical convex-order comparison between the tilted law and the binomials with $r$ and $d$ trials and the same mean. [Variance attribution and review](independent-review.md#engset-source-and-variance-comparisons)

## The carried-load substitution

Set $G_a(z)=\sum_{j=0}^{a}\binom{d-1}{j}z^j$. Pascal's identity gives $G=G_r+zG_{r-1}$, and the numerator of the mean divided by $d$ is $zG_{r-1}/G$. Hence

$$
\frac{x}{1-x}=\frac{zG_{r-1}}{G_r},\qquad
e^{-g}=\frac{G_{r-1}}{G_r}=1-B,
\qquad
B=\frac{\binom{d-1}r z^r}{G_r(z)}.
$$

Here $B$ is Engset call congestion at the idle-source intensity $z$. Write $y=1/z$,

$$
H(y)=\frac{y^rG_r(1/y)}{\binom{d-1}r},\qquad
U(y)=\frac{H(y)-1}{y},\qquad
\delta=\frac1{U(y)},\qquad
w=\frac{1-x}{x}=y+\delta .
$$

The coefficients of $U$ are $u_i=\binom{d-1}{r-1-i}/\binom{d-1}{r}$ for $0\le i\le r-1$, so they are positive and log-concave. Also $g=\log(w/y)$.

Azimzadeh–Carpenter Lemma 2 is about their fixed-point map at fixed offered load $\alpha$, with argument the trial blocking probability and inverse intensity $1/\alpha-1+P$. It does not give carried-load convexity directly. Their Theorem 7 can supply $\delta''\ge0$: $U/u_0={}_2F_1(1,-(r-1);d-r+1;-y)$, and its derivative is a positive multiple of their $h_1$. The stated decrease of $h_1/h_0^2$ implies the convexity of $1/U$. The cap $r=1$ has constant $U$. The next argument proves this input directly. [Azimzadeh–Carpenter, Fast Engset computation, corrected v5](https://arxiv.org/abs/1511.00291v5) · [Version of record](https://doi.org/10.1016/j.orl.2016.02.011)

## Reciprocal convexity from log-concave coefficients

For any polynomial $U(y)=\sum_i u_i y^i$ with nonnegative log-concave coefficients of interval support, the coefficient of $y^{N-2}$, for $N\ge2$, in $2(U')^2-UU''$ is

$$
\sum_{i=0}^N \bigl(3i(N-i)-N(N-1)/2\bigr)u_i u_{N-i},
$$

where out-of-range coefficients are zero. The bracket is symmetric, increases toward the midpoint, and sums to zero over $i=0,\ldots,N$. Log-concavity makes $u_i u_{N-i}$ symmetric and increasing toward that same midpoint: within the support this follows by comparing consecutive $u_{i+1}/u_i$ to $u_{N-i}/u_{N-i-1}$. The support convention handles edge zeros. The two sequences are similarly ordered, so their covariance under the uniform law is nonnegative. Thus every coefficient is nonnegative. Since $(1/U)''=(2(U')^2-UU'')/U^3$, we get $\delta''\ge0$. In the Engset case with $r\ge2$, the constant numerator coefficient is $2(u_1^2-u_0u_2)>0$ by the strict binomial ratios, including $u_2=0$ when $r=2$.

## Chain rule and quantitative control

Primes on $w$ refer to its $y$-derivative. Its positive derivative $w'>0$ follows by the strict monotonicity of the mean and $y=1/z$. Since $\delta'\le0$ and $\delta>0$, $w'\le1$ and $v:=yw'/w\in(0,1)$. Further $w''=\delta''\ge0$. Differentiation in carried load gives

$$
g'(x)=(1+w)^2\left(\frac1{yw'}-\frac1w\right)
       =(1+w)^2\frac{1-v}{y w'}>0 .
$$

To differentiate again, use $dy/dx=-(1+w)^2/w'$ and

$$
\frac{1}{(1+w)^2}\frac{d}{dy}\bigl[g'(x(y))\bigr]
  =(1-v)\left(\frac2{y(1+w)}-\frac{1+v}{y^2 w'}\right)
   -\frac{w''}{y(w')^2}.
$$

Dividing the second derivative's non-$w''$ term by $g'(x)$ gives $(1+w)^2[(1+v)/(yw')-2/(1+w)]=g'(x)+2/(1-x)$. Thus, exactly,

$$
g''(x)=(g'(x))^2+\frac{2g'(x)}{1-x}
             +\frac{(1+w)^4 w''}{y(w')^3}.
$$


Since $g'=d/V-1/[x(1-x)]>0$, the variance upper bound follows. Put $J=g'+1/(1-x)=d/V-1/x>0$. The differential inequality implies $J'\ge J^2$. On approaching $x=\rho$, $S$ concentrates at $r$ and $J\to\infty$. Integrating $(1/J)'\le-1$ to that endpoint gives $J(x)\le1/(\rho-x)$, establishing the variance lower bound. More locally, for $0<x<x'<\rho$,

$$
\frac1{J(x)}-\frac1{J(x')}\ge x'-x,\qquad
\kappa_3(S)\le \frac{2V^2}{dx}-V,
$$

where the cumulant inequality uses $dV/dx=d\kappa_3/V$ in $J'\ge J^2$. For $r=d$ the model is binomial and $g=0$; for $r=0$ there is no open carried-load interval.

These estimates apply to the saddle entropy obtained from $G(z)$. They do not bound the finite balanced-column conditioning error by themselves.
