# Independent agent-assisted review of the symmetric weight obstruction

The symmetric weighting with singleton weight $\tau/\sqrt n$ and pair and empty weights $1$ gives a conjugate pair of nonreal quota roots for every sufficiently small fixed $\tau>0$ and all sufficiently large $n$. The same obstruction occurs when the common pair weight $t$ and the row count satisfy $n\ll t\ll n^{5/2}$, with singleton and empty weights $1$. Here $\ll$ means the ratio of the left side to the right side tends to zero.

## Exact coefficients and uniform convergence

At quota $k$ with $2s$ singleton rows there are $e=2k-s$ pair rows and $L=2k+s$ occupied rows. Let $a_i$ and $b_{ij}$ count each singleton and pair type. On $k$ labeled vertices of each color, first partition the vertices of color $i$ into $a_i$ singleton labels and the $b_{ij}$ labels to be matched to each other color. Pair each of the resulting opposite pools by a bijection. This yields exactly
$$
\frac{(k!)^4}{\prod_i a_i!\prod_{i<j}b_{ij}!}
$$
matchings in $K_{k,k,k,k}$ for those type counts. Hence
$$
c_{k,s}=\frac{m_{2k-s}(K_{k,k,k,k})}{(k!)^4}
$$
is precisely the sum of inverse type factorials. The labeled-row injection contributes $(n)_L$. With $q=z/n^2$ and singleton weight $\tau/\sqrt n$, the finite and limiting functions are
$$
\mathcal F_n(z,\tau)=\sum_{k\ge0}\sum_{s=0}^{2k}
c_{k,s}z^k\tau^{2s}\frac{(n)_{2k+s}}{n^{2k+s}},
\qquad
\mathcal F(z,\tau)=\sum_{k\ge0}\sum_{s=0}^{2k} c_{k,s}z^k\tau^{2s}.
$$
The row factor is interpreted as zero for $L>n$.

The number of matchings is at most the corresponding count in the complete graph on $4k$ vertices. Its bound gives
$$
c_{k,s}\le
\frac{(4k)!}{(k!)^4(2s)!2^e e!}
\le\frac{4096^k}{(2k)!}.
$$
For the second inequality use $(4k)!/(k!)^4\le4^{4k}$ and $(2s)!e!\ge (2k+s)!/2^{2k+s}\ge(2k)!/2^{4k}$. This majorizes the series on every complex compact set even after multiplying terms by any fixed polynomial in $L$, since $L\le4k$ and each $k$ has $2k+1$ summands.

The ratio $(n)_L/n^L$ is the probability that $L$ independent uniform row labels are distinct. The union bound and the first two Bonferroni bounds yield
$$
0\le 1-\frac{(n)_L}{n^L}\le\frac{\binom L2}{n},\qquad
0\le\frac{(n)_L}{n^L}-1+\frac{\binom L2}{n}
\le \frac{\binom{\binom L2}{2}}{n^2}.
$$
Distinct unordered pairs of equal-label events have intersection probability $1/n^2$ even when the two pairs share a label. This proves local uniform convergence, with error $O_K(1/n)$, and gives a local uniform expansion with the first correction of order $1/n$ and a remainder $O_K(1/n^2)$.

## Splitting the triple root

Let $F(z)=\sum_{k\ge0}z^k/(k!)^2$ and $G=F'$. With no singletons, opposite pairs have equal multiplicities, so $\mathcal F(z,0)=F(z)^3$. Two distinct singleton colors give one forced edge on the two other colors, and there are six choices of two colors. Two singleton rows of one color give a forced triangle on the three other colors, and the singleton type factorial is $2!$. Hence
$$
\mathcal F(z,\tau)
=F(z)^3+\tau^2\bigl(6zG(z)F(z)^2+2z^2G(z)^3\bigr)+O_K(\tau^4).
$$

Take a simple negative zero $a$ of $F$. These zeros correspond to the simple positive zeros of $J_0$ under $F(-x^2)=J_0(2x)$. On replacing $z$ by $a+\tau^{2/3}w$ and dividing by $\tau^2G(a)^3$, the right side tends to $w^3+2a^2$ as $\tau\downarrow0$, locally uniformly in $w$. Two of its three roots are simple and nonreal. Place disjoint disks off the real axis around those two roots. Rouché's theorem gives one zero in each disk for all sufficiently small fixed $\tau>0$, and the local uniform convergence of $\mathcal F_n$ then gives the same conclusion for all sufficiently large $n$. [Bessel zeros](https://dlmf.nist.gov/10.21)

## The finite-size splitting scale

Write $f=F^3$. With $\tau=0$, the coefficient of the $1/n$ correction from the exact row factors is
$$
-\sum_k\binom{2k}{2}[z^k]f(z)\,z^k=-2z^2f''(z)-zf'(z).
$$
At small $\tau$, the nonzero-singleton part of this correction is $O_K(\tau^2)$. Thus at $z=a+\delta$ we have
$$
\begin{aligned}
\mathcal F_n(a+\delta,\tau)/G(a)^3
={}&\delta^3+2a^2\tau^2-\frac{12a^2\delta}{n}\\
&+O\left(|\delta|^4+\tau^2|\delta|+\tau^4+
\frac{|\delta|^2+\tau^2}{n}+\frac{1}{n^2}\right)
\end{aligned}
$$
on a fixed small disk in $\delta$, with real small $\tau$. If $\tau=\tau_n\to0$ and $n\tau_n^{4/3}\to\infty$, set $\delta=\tau_n^{2/3}w$ and divide by $\tau_n^2$. Every error tends to zero locally uniformly, the finite-size linear term disappears, and the two nonreal zeros persist.

At $\tau=\kappa n^{-3/4}$ with fixed $\kappa\ge0$, the scaling $\delta=n^{-1/2}w$ instead gives
$$
n^{3/2}\mathcal F_n(a+n^{-1/2}w,\kappa n^{-3/4})/G(a)^3
\ \longrightarrow\ w^3-12a^2w+2a^2\kappa^2.
$$
The discriminant is $108a^4(64a^2-\kappa^4)$. When $\kappa^2>8|a|$, there are two nonreal roots in this cluster for all sufficiently large $n$. When $\kappa^2<8|a|$, the three roots in the cluster are real and simple for all sufficiently large $n$. To see the second assertion, take disjoint conjugation-invariant disks about the three simple real limiting roots. Each disk contains just one zero, which must be real by conjugation. The equality case needs a higher-order calculation.

## Relation to the original weighting

Multiplying each occupied cell by $\tau/\sqrt n$ converts the model with singleton weight $1$ and pair weight $t=n/\tau^2$ to the model above. At quota $k$ this introduces a common coefficient factor $(\tau/\sqrt n)^{4k}$, which merely rescales the quota variable by a positive constant. The condition $\tau_n\to0$ and $n\tau_n^{4/3}\to\infty$ is therefore exactly $n\ll t\ll n^{5/2}$.

For fixed pair weight $t$, including the original $t=1$, the natural initial scaling with singleton weight $1$ is instead $q=z/n^4$. At quota $k$, each term with $e$ edges then has weight $(t/n)^e$ times the bounded row ratio $(n)_{4k-e}/n^{4k-e}$. The same majorant proves local uniform convergence to
$$
\sum_{k\ge0}\frac{z^k}{(k!)^4},
$$
because only $e=0$ survives and the four singleton counts are all $k$. This limit already belongs to the Laguerre–Pólya class. The sequence $1/k!$ is a multiplier sequence by the Pólya–Schur criterion applied to its exponential generating function $F$. Apply that sequence three times to $(1+z/N)^N$. The resulting polynomials are real-rooted and converge locally uniformly to the displayed limit by coefficient domination. Thus this necessary limit condition for the original real-rootedness conjecture passes. The nonreal-root obstruction excludes a uniform theorem covering all positive symmetric pair weights. [Pólya and Schur, 1914](https://doi.org/10.1515/crll.1914.144.89)
