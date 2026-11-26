# Independent certificate for an obstruction to positive radial dilation

Agent-assisted review by Codex (`edge_referee`), 2026-11-26.

I accept the obstruction at dimension $`9`$ and cap $`4`$. For every sufficiently large height $`n`$, the coefficient ratios for the unshifted section of the capped row polynomial cannot be represented by moments of a positive measure on $`[0,\infty)`$. The argument gives the explicit step $`h=1/1500`$ in the limiting quota variable. Its conclusion about height uses a local limit and gives an existential threshold.

## Exact derivative and interval certificate

Let $`S`$ have probabilities proportional to $`\binom9s w^s`$ for $`0\le s\le4`$. At $`v=1/w`$ write $`x=4-\mathbb E S`$ and $`a=\mathbb E[S(9-S)]/72`$. In the variable $`v`$, set

$$
B(v)=126+84v+36v^2+9v^3+v^4,\qquad C(v)=35+21v+7v^2+v^3.
$$

The coefficients of $`B`$ correspond to $`4-S`$, so $`x(v)=vB'(v)/B(v)`$ and $`a(x(v))=C(v)/B(v)`$. Thus $`a(0)=5/18`$ and $`g(x(v))=(5/18)^4 B(v)^4/C(v)^4`$. The derivative of $`x(v)`$ is $`Q(v)/B(v)^2`$, where

$$
Q=(vB')'B-v(B')^2=10584+18144v+13230v^2+5040v^3+1080v^4+144v^5+9v^6.
$$

It is strictly positive for $`v\ge0`$, so $`x`$ is an analytic coordinate near the closed endpoint $`v=0`$. By the chain rule,

$$
g^{(m)}(x(v))=(5/18)^4\frac{P_m(v)}{C(v)^{4+m}Q(v)^{2m}},\qquad P_0=B^4,
$$

where the integer-polynomial recurrence is

$$
P_{m+1}=B^2\left[C Q P'_m-\big((4+m)C'Q+2m C Q'\big)P_m\right].
$$

This differentiates in $`v`$ directly and divides by $`x'(v)`$ at every step. For $`P_8(v)=\sum_i c_i v^i`$ and $`u=1/100`$, define $`U=c_0+\sum_{i\ge1}\max(c_i,0)u^i`$. The exact-arithmetic checker evaluates the recurrence and certifies

$$
g^{(8)}(0)=-\frac{8846065132029}{58824500000},\qquad
(5/18)^4 U<-60 C(u)^{12}Q(u)^{16},\qquad
x(u)=\frac{84722704}{12684360901}>\frac9{1500}.
$$

For $`0\le v\le u`$ we have $`P_8(v)\le U<0`$. The positive denominator $`C(v)^{12}Q(v)^{16}`$ is at most its value at $`u`$ by nonnegativity of the coefficients of $`C,Q`$. Dividing therefore gives $`g^{(8)}(x)<-60`$ for $`0\le x\le x(u)`$. With $`h=1/1500`$, all the test points $`h,2h,\ldots,9h`$ are interior. Repeated integration of the derivative yields

$$
\Delta_h^8 g(h)=\int_{[0,h]^8}g^{(8)}(h+t_1+\cdots+t_8)\thinspace{}dt_1\cdots dt_8<-60h^8.
$$

Run `python3 -IB verify_derivative.py` in this directory to reproduce the derivative and interval certificate using only integer polynomial operations and rational comparisons. [Exact checker](verify_derivative.py)

## Local limit at the nine fixed interior quotas

Let $`H(z)=\sum_{s=0}^4\binom9s z^s`$, $`A_m=[z^m]H(z)^n`$, and let $`a_{n,k}`$ count labeled capped arrays with every column sum $`k`$. On the range $`0\le k\le\lfloor4n/9\rfloor`$ put $`p_{n,k}=a_{n,k}/A_{9k}`$. For a fixed $`w\in(0,\infty)`$ let the random row $`X`$ have probabilities $`w^{|X|}/H(w)`$ on binary vectors of size at most four. Then, with $`X_i`$ independent and $`S_i=|X_i|`$,

$$
p_{n,k}=\frac{\mathbb P(\sum_{i=1}^n X_i=k\mathbf 1)}{\mathbb P(\sum_{i=1}^n S_i=9k)}.
$$

The common probability factor for any array with total size $`9k`$ is $`w^{9k}/H(w)^n`$, so it cancels. The support of $`X`$ contains $`0`$ and the nine coordinate unit vectors. Its difference lattice is $`\mathbb Z^9`$, and its characteristic function has modulus one only at the origin modulo $`2\pi\mathbb Z^9`$. Likewise $`S`$ has span one because its support contains $`0,1`$. Both lattice volume factors are one. If $`\mu=\mathbb E S`$ and $`\sigma^2=\mathrm{Var}(S)`$, the exchangeable covariance matrix of $`X`$ has eigenvalue $`\sigma^2/9`$ in the unit direction of $`\mathbf1`$. On the orthogonal complement its eigenvalue is

$$
\mathbb E X^{(1)}-\mathbb E X^{(1)}X^{(2)}
=\mathbb E\left[\frac S9-\frac{S(S-1)}{9\cdot8}\right]=a(x).
$$

Both eigenvalues are positive for finite positive $`w`$. For targets $`9k-n\mu=O(1)`$, Fourier inversion near the origin gives the central Gaussian density times $`n^{-9/2}`$ for the numerator and $`n^{-1/2}`$ for the denominator. In each inversion the characteristic function to the power $`n`$ decays exponentially outside a fixed neighborhood of zero by the support calculation. In that neighborhood, subtracting the mean from the phase and scaling angles by $`n^{-1/2}`$ leaves the Gaussian with the stated covariance, with Gaussian domination from positivity of the covariance. The bounded target deviations contribute a phase tending to one. The resulting ratio is

$$
p_{n,k}\sim\frac{(2\pi n)^{-9/2} a(x)^{-4}(\sigma^2/9)^{-1/2}}{(2\pi n)^{-1/2}(\sigma^2)^{-1/2}}=3(2\pi n)^{-4}a(x)^{-4}.
$$

Choose $`k_n=\lfloor n(4-9h)/9\rfloor`$ and $`b_n=\lfloor nh/9\rfloor`$. For all sufficiently large $`n`$, $`b_n\ge1`$ and $`1\le k_n\le k_n+8b_n<\lfloor4n/9\rfloor`$. For each $`0\le j\le8`$, the target $`k_n+j b_n`$ differs by a bounded amount from $`n(4-(9-j)h)/9`$. Apply the ratio estimate at the fixed interior tilt with $`x=(9-j)h`$. The normalized ratios satisfy

$$
\frac{(2\pi n)^4 a(0)^4}{3}\thinspace{}p_{n,k_n+j b_n}\longrightarrow g((9-j)h).
$$

No congruence on $`n`$ is needed since each of the nine applications is in the interior on the full lattice. The derivative was evaluated at the closed endpoint to locate an interval of strict sign.

## Moment inequality and scope

For any positive measure on $`[0,\infty)`$ that represents $`p_{n,k}`$ at the required indices, the binomial identity gives

$$
\sum_{j=0}^8(-1)^j\binom8j p_{n,k+j b}=\int t^k(1-t^b)^8\thinspace{}d\mu(t)\ge0
$$

for integers $`k,b\ge1`$ with the nine moments finite. At $`k=k_n,b=b_n`$, the normalized sum converges to $`\sum_{j=0}^8(-1)^j\binom8j g((9-j)h)=\Delta_h^8g(h)`$. The order is even, so reversing the test points preserves their signs in the sum. The strict negative bound contradicts the moment inequality for every sufficiently large height.

In particular a positive radial dilation mixture of the section $`\sum_k A_{9k} q^k`$ would represent these ratios by moments, by comparing coefficients with $`\sum_k a_{n,k}q^k`$. The obstruction allows arbitrary nonnegative dilation scales and a measure depending on the height. The coefficient alignment is the unshifted section of $`H^n`$.
