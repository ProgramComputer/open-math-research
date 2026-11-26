# A lattice estimate when the row variance tends to zero

Let $X$ have a log-concave probability mass function on an interval of integers, with mean $\mu$ and variance $V>0$. Let $L$ be the probability that the sum of $n\ge2$ independent copies of $X$ equals $n\mu$, assumed integral. The [large-variance lattice bound](../uniform-lattice-lemma.md) proves that for $V\ge1$ the relative error in $L\sim(2\pi nV)^{-1/2}$ is $O(n^{-1/2})$, with an absolute constant. It also proves $\mathbb E|X-\mu|^3\le C V^{3/2}$ in this range. Here we give the complementary bounds for $0<V\le1$. The distribution in the application has finite support.

Write $p_j=\mathbb P(X=j)$, choose a mode $m$, and let $b=p_m$. Chebyshev puts mass at least $3/4$ on $[\mu-2,\mu+2]$, which contains at most five integers. Hence $b\ge3/20$. On each side let $h$ be the first positive distance from the mode where the probability is at most $b/2$, setting missing probabilities to zero. Since every preceding mass on that side is greater than $b/2$, $h$ is bounded by a numerical constant. Up to distance $h$ the mass is at most the adjacent probability on that side. Beyond $h$ log-concavity gives $p_{m+j}\le p_{m+1}2^{-(j-h)/h}$ on the right, with the corresponding left estimate. If the support ends at or before $h$ the tail is zero. For $s=2,3$ we deduce

$$
\mathbb E|X-m|^s\le C_s(p_{m-1}+p_{m+1})\le C_s(1-b).
$$

For independent copies $X,X'$, the identity $V=\mathbb E(X-X')^2/2$ implies $V\ge b(1-b)$ by retaining the pairs with just one coordinate at the mode. Jensen and the triangle inequality give $\mathbb E|X-\mu|^3\le C V$. Conversely $V\le\mathbb E|X-m|^2$ shows that $p_{m-1}+p_{m+1}\ge cV$. If $\phi(t)=\mathbb E e^{it(X-\mu)}$, the mode and its two neighbors in the cosine expansion of $1-|\phi(t)|^2$ give $|\phi(t)|\le e^{-c Vt^2}$ for $|t|\le\pi$. Taylor's formula and $V\le1$ give

$$
|\phi(t)-e^{-Vt^2/2}|\le C V|t|^3\qquad (|t|\le\pi).
$$

Telescoping the powers of order $n$ gives an integrated error $O(1/(nV))$ on this interval using the Gaussian bound for each of the remaining $n-1$ factors. If $nV\ge1$, the omitted Gaussian tails outside the interval have at most this same order. Fourier inversion at the integer mean then yields

$$
L=(2\pi nV)^{-1/2}\left(1+O((nV)^{-1/2})\right).
$$

Finally, in an interior exponential tilt with parameter $\lambda$, $d\mu/d\lambda=V$ and $dV/d\lambda=\mathbb E(X-\mu)^3$. The two third-moment bounds, for $V$ on either side of one, show $|dV/d\mu|\le C(1+\sqrt V)$. This applies to the capped-binomial family throughout the open feasible interval.
