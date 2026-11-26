# Uniform root-circle bounds for the full-rank polynomial

For integers $n,d\ge2$, let

$$
F(q)=F_{n,d}(q)=\sum_{k=0}^n\binom nk^d q^k.
$$

Write its zeros as $-\rho_1,\ldots,-\rho_n$, with $0<\rho_1<\cdots<\rho_n$. They are all simple, and

$$
\log\rho_{i+1}-\log\rho_i\ge\frac{2\pi}{\sqrt{n(n+1)}}.
\tag{1}
$$

At every $t>0$, the probability law $\Pr(K=k)=\binom nk^d t^k/F(t)$ satisfies

$$
\mathrm{Var}(K)\le C(1+n/d)
\tag{2}
$$

for an absolute constant $C$. Finally, on the circle $|z+\rho_i|=e^{-h}\rho_i$ with $e^{-h}\le1/(4n)$, let $K_t$ be the tilted law at $t=|z|$. With absolute constants,

$$
\begin{aligned}
\frac{|F(z)|}{F(|z|)}
&\ge \exp\bigl[-h-C'(1+\mathrm{Var}(K_t))\log(n+1)\bigr]\\
&\ge \exp\bigl[-h-C''(1+n/d)\log(n+1)\bigr].
\end{aligned}
\tag{3}
$$

All statements hold in particular throughout $2\le d\le n$.

## Logarithmic root spacing

Rodrigues' formula for the Legendre polynomial $L_n$, expanded by Leibniz's rule, gives

$$
L_n(x)=2^{-n}\sum_{k=0}^n\binom nk^2(x-1)^k(x+1)^{n-k}.
$$

Thus $F_{n,2}(q)=(1-q)^nL_n((1+q)/(1-q))$. Orthogonality of $L_n$ to all lower-degree polynomials on $[-1,1]$ follows by integration by parts in Rodrigues' formula. If it had fewer than $n$ sign-change roots in this interval, their linear factors would form a lower-degree polynomial whose product with $L_n$ has constant nonzero sign off its zeros, contradicting orthogonality. Consequently $F_{n,2}$ has $n$ simple negative zeros.

Write $y=\log\rho$ at $q=-\rho$, so the Legendre argument is $x(y)=-\tanh(y/2)$. Then $x'=-(1-x^2)/2$. The Legendre equation $((1-x^2)L_n')'=-n(n+1)L_n$ implies for $f(y)=L_n(x(y))$ that

$$
f''(y)+\frac{n(n+1)}{4\cosh^2(y/2)} f(y)=0.
$$

On an interval between consecutive zeros of $f$, of length $\ell$, multiply by $f$ and integrate by parts. The endpoint terms vanish. The Dirichlet inequality gives

$$
\left(\frac{\pi}{\ell}\right)^2\int f^2
\le\int (f')^2
=\int\frac{n(n+1)}{4\cosh^2(y/2)}f^2
\le\frac{n(n+1)}4\int f^2.
$$

This proves (1) for $d=2$. In degree $n$ the Schur–Szegő product is coefficientwise multiplication on the coordinates relative to $\binom nk q^k$, so $F_{n,d+1}=F_{n,d}*F_{n,2}$. The same-sign real-rootedness and logarithmic mesh theorem applies to the two factors of degree $n$ and preserves the lower bound on the minimum successive root ratio. The resulting positive coefficients and nonzero constant term force all real zeros to be negative. Induction gives (1), including simplicity. [Katkova, Shapiro and Vishnyakova, Theorems 4 and 6](https://doi.org/10.1016/j.crma.2010.11.031)

## Tilted variance

Let $b_k=\binom nk^d t^k$ and $R_k=b_k/b_{k-1}$. At every internal index,

$$
\log(R_k/R_{k+1})
=d\bigl[\log(1+1/k)+\log(1+1/(n-k))\bigr]
\ge \frac{4d}{n+2}.
$$

Here $\log(1+1/j)\ge1/(j+1)$ and the two denominators sum to $n+2$. In particular the curvature is at least $\lambda=\min(1,d/n)$. Choose any mode $m$ of $b$. The first outward ratio on either side of $m$ is at most one. For $j\ge0$ the ratio of the mass at outward distance $j+1$ to that at distance $j$ is at most $e^{-\lambda j}$, by multiplying the successive curvature bounds. This applies separately to the laws of $K-m$ conditional on $K\ge m$ and $m-K$ conditional on $K\le m$.

Compare either one-sided law to the reference law on the nonnegative integers with weights $g_j=e^{-\lambda j(j-1)/2}$. Its likelihood ratio relative to this reference is nonincreasing, including after setting the candidate weights to zero outside their support. A nonincreasing likelihood ratio implies stochastic domination by the reference law. For example, the covariance of the likelihood ratio and an increasing test function under the reference is nonpositive by the independent-copy covariance formula. The reference normalization is at least $\sum_{j\ge0}e^{-\lambda j^2/2}\ge c\lambda^{-1/2}$. Its unnormalized second moment is $O(\lambda^{-3/2})$ by $j(j-1)/2\ge j^2/4$ for $j\ge2$ and Gaussian sum bounds. Each conditional second moment about $m$ is therefore $O(\lambda^{-1})$. Combining the two sides and using $\mathrm{Var}(K)\le\mathbb E(K-m)^2$ proves (2).

Independently, the factorization gives the probability generating function

$$
\frac{F(tz)}{F(t)}=
\prod_{j=1}^n\left[(1-p_j)+p_jz\right],
\qquad p_j=\frac{t}{t+\rho_j}.
$$

Thus $K$ is distributed as a sum of independent Bernoulli variables and

$$
\mathrm{Var}(K)=\sum_{j=1}^n p_j(1-p_j)
=\sum_{j=1}^n\frac{1}{4\cosh^2((\log\rho_j-\log t)/2)}.
\tag{4}
$$

## Product bound on each circle

Put $\epsilon=e^{-h}$, $t=|z|$, and $y_j=\log\rho_j-\log t$. On $|z+\rho_i|=\epsilon\rho_i$, the reverse triangle inequality gives $1-\epsilon\le t/\rho_i\le1+\epsilon$. Hence $|\log(t/\rho_i)|\le2\epsilon$, and the centered factor satisfies

$$
\frac{|1+z/\rho_i|}{1+t/\rho_i}=\frac{\epsilon}{1+t/\rho_i}\ge\frac{\epsilon}{3}.
$$

For $j\ne i$, (1) and $2\epsilon\le1/(2n)$ imply $|y_j|\ge 1/n$. The reverse triangle inequality gives the positive bound

$$
\frac{|1+z/\rho_j|}{1+t/\rho_j}
\ge\frac{|1-t/\rho_j|}{1+t/\rho_j}
=\tanh(|y_j|/2).
$$

For $|y_j|\le1$ this bound is at least $c_1/n$, and its negative logarithm is $O(\log(n+1))$. There are at most $C_1\mathrm{Var}(K)$ such indices by (4), since each contributes a uniformly positive term to that sum.

For $|y_j|>1$ put $a=e^{-|y_j|}\le e^{-1}$. The negative logarithm of the bound is $\log((1+a)/(1-a))\le 2a/(1-a)=O(a)$. Since $p_j(1-p_j)=a/(1+a)^2\ge a/4$, the sum of these negative logarithms is $O(\mathrm{Var}(K))$. Thus the product of all factors except the centered one has negative logarithm $O(\mathrm{Var}(K)\log(n+1))$. Including the centered factor adds at most $h+\log3$, proving the first bound in (3). Applying (2) gives the second bound.

The circles bound pairwise disjoint disks by (1), since for adjacent radii the relative separation $(\rho_{j+1}-\rho_j)/(\rho_{j+1}+\rho_j)$ equals the hyperbolic tangent of half the log-gap and exceeds $\epsilon$. Each disk is invariant under conjugation and lies in the open left half-plane. Consequently a real-coefficient perturbation satisfying the corresponding strict Rouché inequality on any selected circles has one simple negative root in each selected disk. This conclusion is local to those circles. A capped polynomial can have degree smaller than $n$, so a separate argument must identify which disks admit that perturbation estimate.
