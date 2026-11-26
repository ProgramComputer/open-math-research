# Negative-binomial normalization of the scalar row-deficit count

Let $B(t)=\sum_{j=0}^r b_jt^j$ with positive, log-concave coefficients, and let $n\ge1$. Set $U_{n,e}=[t^e]B(t)^n$. Then

$$
\frac{U_{n,e}}{\binom{n+e-1}{e}}
\qquad (0\le e\le nr)
$$

is log-concave. The claim includes $r=0$, when its support is a singleton, and $n=1$, when the denominator is one.

## Size-biased proof

Take $n\ge2$ and set $C_m=U_{n-1,m}$, extended by zero outside its support. Ordinary convolution preserves log-concavity of sequences with interval support, so $C_m$ is log-concave with positive support $[0,(n-1)r]$. [Hoggar, 1974](https://doi.org/10.1016/0095-8956%2874%2990071-9) · [Johnson and Goldschmidt, Theorem 1.4](https://www.numdam.org/article/PS_2006__10__206_0.pdf#page=2)

Put $b_{r+1}=0$. The probability on $j\in\lbrace 0,\ldots,r\rbrace$ proportional to $(j+1)b_jC_{e-j}$ will be denoted by $\pi_e$. Its normalizing constant and the coefficient derivative identity are

$$
\begin{aligned}
\sum_j (j+1)b_j C_{e-j}&=(1+e/n)U_{n,e},\\
\sum_j (j+1)b_{j+1} C_{e-j}&=(e+1)U_{n,e+1}/n.
\end{aligned}
$$

For the first identity, the sum without the factor $j$ is the scalar coefficient convolution. With the factor $j$, row symmetry gives a share $1/n$ of the total deficit $e$ in each term. For the second identity compare coefficients at $t^e$ after differentiating $B^n$. Hence

$$
\mathbb E_{\pi_e}\frac{b_{j+1}}{b_j}
=\frac{(e+1)U_{n,e+1}}{(n+e)U_{n,e}}.
$$

As $e$ increases by one, $\pi_e$ increases in likelihood-ratio order. In fact, for $i<j$ the cross-product inequality for the unnormalized laws reduces to

$$
C_{e+1-j}C_{e-i}\ge C_{e-j}C_{e+1-i}.
$$

If the right side is positive, both indices on the left lie between the right-hand indices in the positive interval. The inequality then follows from decreasing consecutive ratios of $C$, and it is immediate if the right side is zero. Thus the likelihood-ratio comparison holds throughout the two possibly different supports. This conditioning argument is related to Efron’s monotonicity theorem. [Efron, 1965](https://doi.org/10.1214/aoms/1177700288) For any decreasing test function $f$, pairing the terms with $i<j$ in the double sum for $\mathbb E_{\pi_{e+1}}f-\mathbb E_{\pi_e}f$ gives terms $(\pi_{e+1}(j)\pi_e(i)-\pi_{e+1}(i)\pi_e(j))(f(j)-f(i))\le0$. Apply this to $f(j)=b_{j+1}/b_j$, which decreases by log-concavity and has value zero at $r$. The displayed normalized forward ratio therefore decreases throughout the support, including the final ratio zero at $e=nr$. This is exactly the claimed log-concavity.

Equivalently, the sum of $n$ independent identically distributed log-concave counts is log-concave relative to the negative binomial distribution with shape $n$, since a geometric factor in the normalizer does not affect log-concavity. Yu's discussion of relative log-concavity under convolution provides related context. His Theorem 11 has the negative binomial comparison in the reverse direction, with different hypotheses. This note makes no priority claim. [Yu, Bernoulli 16 (2010), §2.3, Theorem 11](https://doi.org/10.3150/09-BEJ216)

## Exact $d$-step bound

For positive integers $d$ and $d\le e\le nr-d$, comparing the normalized consecutive ratios over $d$ steps gives

$$
\frac{U_{n,e}^2}{U_{n,e-d}U_{n,e+d}}
\ge
\prod_{i=1}^d
\frac{(e+i)(n+e-d+i-1)}{(e-d+i)(n+e+i-1)}.
$$

The logarithm of the factor at index $i$ is the integral, for $0\le t\le d$, of

$$
\frac{n-1}{(e-d+i+t)(n+e-d+i-1+t)}.
$$

Since the second denominator is at most $n+e+d-1$ and $e-d+i\le e$, the log of the exact product is at least

$$
\frac{d(n-1)}{n+e+d-1}\log(1+d/e).
$$

When $e+d\le d(n-1)$ this is at least the [proposed array bound](README.md) $nd\log(1+d/(e+d))/(n+e+d)$. Indeed comparing the integral formulas for the two logarithms gives $\log(1+d/e)\ge(1+d/(e+d))\log(1+d/(e+d))$. The resulting prefactor comparison is equivalent to $d(n-1)(n+e+d)\ge(e+d)^2$. For proper array cap $r<d$ with $n\ge d$, the required $e+d\le d(n-1)$ follows from $e+d\le nr\le n(d-1)$ at an internal quota.

## Conditioning on equal column sums

For the array row-deficit law take $b_j=\binom d{r-j}$. The scalar count $U_{n,e}$ includes every array of total deficit $e$, and the coefficient at common quota $k=(nr-e)/d$ is $U_{n,e}$ times the probability of equal column sums under that scalar count. A transfer requires quantitative control of the second differences of the logarithm of this conditioning probability.

For instance, at rank one the exact conditional factor is $c_k=(dk)!/(d^{dk}(k!)^d)$. Its forward ratio is

$$
\frac{c_{k+1}}{c_k}
=\prod_{i=1}^d\left(1-\frac{d-i}{d(k+1)}\right),
$$

strictly increasing when $d\ge2$. Thus a transfer through log-concavity of the conditioning factor already fails at rank one. The scalar calculation gives no inequality for the balanced-array counts after conditioning. The transfer question belongs to the [balanced-array investigation](https://github.com/ProgramComputer/open-math-research/issues/2).
