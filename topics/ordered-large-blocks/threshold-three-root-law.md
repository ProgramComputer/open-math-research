# Distribution of zeros at ordered threshold three

Use the pole notation of the [threshold-three theorem](threshold-three.md). The critical size parameter is $v_*$, the positive double pole is $s_*=2\sqrt{v_*}$, and $q_*=v_*^{-1}-1$. For $q>q_*$, write $z(q)$ for the principal pole with positive imaginary part. Write $q_{n,h}$ for the $h$th smallest zero modulus.

**Corollary.** The empirical distribution functions of the zero moduli converge uniformly to $0$ for $q\le q_*$ and to $3\arg z(q)/\pi$ for $q>q_*$. For fixed $h\ge1$,
$$
 \lim_{n\to\infty} n^2(q_{n,h}-q_*)
 =\frac{s_*^3}{2(e^{s_*}-2)v_*^2}\pi^2 h^2 .
$$
The complementary $n^3$ scale at the outer edge is given by the [general exponential-section limit](fixed-threshold-outer-zeros.md).

**Proof.** For $n\ge94$ the threshold-three proof gives a root in each phase band $(h\pi,(h+1)\pi)$, exhausting the degree. At any $q>q_*$ the bands below the current phase have been crossed before $q$, and the bands above it must be crossed after $q$. At the last band in degree $n=3m$ the leading sign at infinity supplies the endpoint whenever the finite upper level is absent. Degree exhaustion and the phase endpoint bounds give, uniformly,
$$
 \#\{h:q_{n,h}\le q\}=(n+1)\arg z(q)/\pi+O(1).
$$
All roots in those rows exceed $q_*$. This proves uniform convergence. The distribution is strictly increasing on its support, by analyticity of the principal branch, monotonicity inherited from the counts, and the different endpoint values.

At fixed $h$ the band gives $\arg z(q_{n,h})=O(1/n)$, hence $q_{n,h}\to q_*$. Near $q_*$ the ratio of the principal modulus to the negative-real pole modulus is bounded strictly below one by (6) in the threshold-three proof, as $R$ tends to a positive value. The contributions of that real pole and the distant complex poles therefore tend to zero uniformly there. The root phase is consequently $(h+1/2)\pi+o(1)$. As $\arg D'_v(z)\to\pi/2$, we get $(n+1)\arg z\to h\pi$.

At the positive double pole, $D_{zz}=s_*>0$ and $\partial_v D=2-e^{s_*}<0$. The latter sign also follows from $e^{s_*}=(1+s_*)/(1-s_*^2/4)$ and $s_*>1$: the defining function $2\sqrt v-\log(1+2\sqrt v)+\log(1-v)$ is positive at $v=1/4$ because $e>8/3$. For $v<v_*$ near $v_*$ the two nonreal poles split from this double zero. Since $\partial_vD\ne0$, one can solve analytically for $v=v(z)$ there. Its Taylor series is
$$
 v-v_* = \frac{s_*}{2(e^{s_*}-2)}(z-s_*)^2+O((z-s_*)^3).
$$
The two square-root branches thus have $\theta=\Im z\sim\sqrt{2(e^{s_*}-2)(v_*-v)/s_*}$ and $\arg z\sim\theta/s_*$. Finally $v_*-v\sim v_*^2(q-q_*)$, yielding the asserted limit. $\square$
