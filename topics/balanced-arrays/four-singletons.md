# Fixed singleton counts and the four-singleton Bessel reduction

Consider balanced four-column arrays with row cap two. Give a row on two colors $ij$ a fixed nonnegative weight $w_{ij}$. A singleton row is supported on exactly one color. The quota variable is $q$.

## Fixing every singleton count

Let $s_i$ count the singletons of color $i$, with $\sum_i s_i=2s$. An odd sum is impossible because the total number of ones is $4k$. For each of the three opposite-edge pairs $ij\mid kl$, set
$$
\delta_{ij}=\frac{s_k+s_l-s_i-s_j}{2}=s-s_i-s_j,\qquad
d_{ij}=|\delta_{ij}|,\qquad D=\sum d_{ij},\qquad k_0=\frac{s+D}{2}.
$$
The three signed differences through color one sum to $s-2s_1$, so $k_0$ is an integer.

If $d_i$ is the degree of color $i$ among the two-color rows and $E$ is their total count, then $d_i+d_j=E+e_{ij}-e_{kl}$. The degree conditions $d_i=k-s_i$ therefore force $e_{ij}-e_{kl}=\delta_{ij}$. Conversely, put
$$
e_{ij}=m_{ij}+\max(\delta_{ij},0),\qquad
e_{kl}=m_{ij}+\max(-\delta_{ij},0),\qquad m_{ij}\ge0 .
$$
For $t=\sum m_{ij}$ and $k=k_0+t$, one has $E=D+2t=2k-s$. The three prescribed pair sums through color one are $d_1+d_j=2k-s_1-s_j$. Together with $\sum_i d_i=2E$ they give $d_i=k-s_i$ for every color. There is no further quota restriction.

The occupied-row count is $2k_0+s+2t$. Put $L=2k_0+s$ and $N=n-L$. If $n\ge L$, the polynomial is $q^{k_0}$ times
$$
\frac{(n)_L}{\prod_i s_i!}
\prod_{ij\mid kl} w_{ij}^{\max(\delta_{ij},0)}w_{kl}^{\max(-\delta_{ij},0)}
\sum_{t\ge0}(N)_{2t}\,[v^t]
\prod_{ij\mid kl}\left(\sum_{m\ge0}
\frac{(w_{ij}w_{kl}v)^m}{m!(m+d_{ij})!}\right)q^t .
$$
This counts the assignments of row types to labeled rows, with each singleton or edge multiplicity divided by its factorial. Interpret $0^0$ as one. The original row polynomial vanishes identically for $n<L$, or if a forced positive edge multiplicity has weight zero. If the displayed prefactor is positive but all three opposite-edge products vanish, the reduced row polynomial is a positive constant.

Otherwise every nonconstant reduced row has simple negative zeros and successive reduced rows strictly interlace. Write $U(v)$ for the three-factor generating series. Each factor in $U(-z^2)$ with $\lambda=w_{ij}w_{kl}>0$ is
$$
\frac{J_{d_{ij}}(2\sqrt{\lambda}\,z)}
     {(\sqrt{\lambda}\,z)^{d_{ij}}},
$$
with the removable value at zero. It has an even canonical product over infinitely many real nonzero zeros. A factor with $\lambda=0$ is $1/d_{ij}!$. [Bessel canonical product, DLMF 10.21.15](https://dlmf.nist.gov/10.21.E15)

The strictness argument applies to any even canonical product $V(z)=U(-z^2)$ with infinitely many zeros and positive constant term. Put $P_N(x)=V(\partial_x)x^N$. Finite products act by factors $1+c\partial_x$ for nonzero real $c$. For a real-rooted polynomial $p$, the function $p'/p$ strictly decreases off its zeros. The equation $p'/p=-1/c$ has one simple solution in every gap and one on the appropriate outer interval. Each root of multiplicity $d$ of $p$ retains multiplicity $d-1$. Thus $p+cp'$ is real-rooted, and maximal multiplicity drops by one unless all roots are already simple. Reserve at least $N-1$ linear factors of the canonical product, taking them in pairs. The remaining product acts on $x^N$ to give a real-rooted polynomial by locally uniform convergence and convergence of its Taylor coefficients. Applying the reserved factors makes the zeros simple for $N\ge1$. The identity $P_{N+1}'=(N+1)P_N$ gives strict interlacing. Since $P_N(x)=x^N$ times the reduced row evaluated at $-1/x^2$, its positive zeros map increasingly onto the reduced negative zeros. For odd $N$ the zero of $P_N$ at zero lies outside this correspondence. Dividing out $q^{k_0}$ excludes the forced quota zeros.

## Summing over two or four singleton rows for uniform edge weights

Set $F(q)=\sum_{m\ge0}q^m/(m!)^2$, $G=F'$, and $H=F''$. The quota series before labeled-row injection for two singleton rows is $q(6GF^2+2qG^3)$. Put $A(u)=F(-u)$ and $R(u)=-A'(u)/A(u)$. The Bessel product gives
$$
R(u)=\sum_{\ell\ge1}\frac{1}{a_\ell-u},\qquad a_\ell=j_{0,\ell}^2/4>0.
$$
Both $R(u)$ and $uR(u)$ have strictly positive imaginary parts in the upper half-plane. The factor $G(-u)=A(u)R(u)$ is nonzero there. A zero of the reflected reduced series would then imply $uR(u)^2=3$, which is impossible because the product of two strictly upper-half-plane numbers cannot be positive real.

For four singletons the coefficient of each count pattern combines the number of permutations and the factor $1/\prod_i s_i!$.

| Counts | $k_0$ | Absolute differences | Contribution before injection |
| --- | --- | --- | --- |
| $4,0,0,0$ | 4 | $2,2,2$ | $q^4H^3/6$ |
| $3,1,0,0$ | 3 | $2,1,1$ | $2q^3HG^2$ |
| $2,2,0,0$ | 2 | $2,0,0$ | $3q^2HF^2/2$ |
| $2,1,1,0$ | 2 | $1,1,0$ | $6q^2G^2F$ |
| $1,1,1,1$ | 1 | $0,0,0$ | $qF^3$ |

Removing $q$ gives
$$
U(q)=F^3+q\left(\tfrac32HF^2+6G^2F\right)+2q^2HG^2+\tfrac16q^3H^3 .
$$
The identity $qF''(q)+F'(q)=F(q)$ gives $uH(-u)=G(-u)-A(u)$. Also $G(-u)=R(u)A(u)$. Substitution yields
$$
\frac{U(-u)}{A(u)^3}
=\frac{16-12R+3R^2-R^3}{6}+(2R-8)uR^2 .
$$
For $u$ in the upper half-plane, $R$ is there too, so $R\ne0,4$. Division and partial fractions show that a zero of $U(-u)$ there would satisfy
$$
\left(u-\frac1{12}\right)R
=\frac1{12}+\frac1{3R}-\frac1{4-R}.
$$
The right side lies strictly in the lower half-plane. The imaginary part of each term $(u-1/12)/(a_\ell-u)$ on the left is $(a_\ell-1/12)\,\mathrm{Im}(u)/|a_\ell-u|^2>0$. Indeed $F(-u)\ge1-u>0$ on $[0,1/12]$ by its alternating series. Thus $U(-u)$ has no upper-half-plane zeros.

For both aggregate series, conjugation excludes lower-half-plane zeros. Nonnegative coefficients and a positive constant term exclude zeros for $u\le0$. Each derivative series $F^{(d)}(-u)$ is bounded by $\exp(2\sqrt{|u|})$, so the reduced aggregate is entire of order at most $1/2$. Its genus-zero Hadamard product has only positive real zeros, and infinitely many because the series is nonpolynomial. Replacing $u$ by $z^2$ gives the even product required by the strictness argument. For the two- and four-singleton slices the common factors are $q(n)_L$, with $L=3$ and $L=4$. The reduced multiplier is $(n-L)_{2t}$. Thus the nonzero roots of each slice are simple negative and strictly interlace across consecutive nonconstant reduced rows.
