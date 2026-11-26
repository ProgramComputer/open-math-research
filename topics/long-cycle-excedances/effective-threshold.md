# An explicit strict-interlacing range with unbounded cycle count

For fixed $3\le k\le n$, let $E_{n,k}(t)$ count permutations of $[n]$ by excedances subject to every cycle having at least $k$ letters. Write $P_n=E_{n,k}/t$. Inversion of a permutation exchanges excedances and deficiencies. A single cycle can attain either extreme, so $P_n$ is reciprocal of degree $n-2$ with constant and leading coefficients one. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Cycle weights and recurrence](two-cycle-band.md)

**Partial theorem.** The zeros of $P_n$ and $P_{n+1}$ are simple, negative and strictly interlace whenever $n\ge10{,}000$ and
$$
k\ge2000\sqrt n\left(3+\log\left(3\sqrt{n/k}\right)\right).
$$
The bound is effective and permits unboundedly many cycles. For example, take $n=2^{4j}$ and $k=2^{3j}$ for any integer $j\ge15$. The condition reduces to $2^j\ge2000(3+\log3+(j/2)\log2)$. Already $2^{15}>2000(5+15/2)$, and doubling the left side at each step preserves the inequality. The largest allowed cycle count is then $2^j$.

## Counting every root

If $n\le3k-2$ this is the [one- and two-cycle theorem](two-cycle-band.md). In the remaining range $n\ge3k-1$, the residual index $m=n+1-k$ is at least $2n/3$ and $m\ge k$. Put $H=\lfloor7\sqrt n/20\rfloor$. The [coefficient argument](effective-front.md) locates the $H$ smallest roots in modulus, all negative and simple, and verifies both insertion signs there. The last of these roots in modulus precedes the sample of index $H+1$.

Parameterize the negative axis by $t=-\exp(-\pi\cot\theta)$ with $0<\theta<\pi$. Then $|t|$ increases with $\theta$. On the first half of the interval take samples $\theta_j=j\pi/n$, starting with $j=H+1$. At this first sample $n\sin^2\theta_j>6/5$. All angles through $\pi/2$ consequently have $n\sin^2\theta\ge1$, $m\sin^2\theta\ge2/3$ and $k\sin\theta\ge2000(3+\log(3\sqrt{n/k}))$. The [separated-pole estimate](separated-poles.md) gives the sample sign $(-1)^j$ for $E_{n,k}$ and controls the insertion term at every old zero in the interval. Reciprocity extends the sample signs, the old-root comparison, and the exterior-root count to the other half. For odd $n$ the central sample gap straddles $\pi/2$ and contains the reciprocal root $-1$.

The consecutive samples with indices $H+1,\dots,n-H-1$ give $n-2H-2$ sign changes. The $2H$ distinct exterior roots exhaust the remaining degree. Thus every gap contains precisely one root and every root is simple. At every old root $x$ we have
$$
P_{n+1}(x)=x(1-x)P'_n(x)+L(x),\qquad
|L(x)|<|x(1-x)P'_n(x)|.
$$
The signs of $P_{n+1}$ there are successively $-1,+1,\dots$ in order of increasing modulus. The positive constant term and the positive leading coefficient, together with $\deg P_{n+1}=n-1$, give both outside roots as well as one new root in each old gap. This proves the strict interlacing.

**Formal coverage.** ⬜ None. The proof is written. The previous uniform eventual theorem has a cutoff independent of $k$ whose numerical value is unknown. The explicit threshold here settles each qualifying pair without computing either polynomial. For smaller $k$ and unrestricted $n$ the full conjecture remains open. [Uniform eventual theorem](uniform-interlacing.md) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)

The independent referee checked the univariate run model, both ends of the root count and the join. Reproduce the rational bounds from the repository root with the command below. [Referee report](review-effective-front.md) · [Scalar checker](verify_front_constants.py)

~~~sh
python3 -I topics/long-cycle-excedances/verify_front_constants.py
~~~
