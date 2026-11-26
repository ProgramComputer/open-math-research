# A bounded-prefix check for the residual three-cycle band

Assume $192\le n\le2199$ and $3k-1\le n<4k$. The middle-angle proof from [the analytic cutoff package](three-cycle-2200.md#sharpened-middle-comparison) applies when $k\sin\theta\ge14$ and $n\sin^2\theta\ge149/100$, provided $n\ge192$ and $k>n/4$. Its calculation on the pole envelopes requires these angular hypotheses, and the threshold 2200 there was only used to deduce them at the previous front join.

Here take the first middle sample at $\theta_{20}=20\pi/n$. Set $u_0=(20/192)(22/7)$. Since $\theta_{20}\le u_0$, the inequality $\sin u\ge u(1-u^2/6)$ for $0\le u\le u_0$ gives

$$
k\sin\theta_{20}>
5\pi(1-u_0^2/6)>14,
\qquad
n\sin^2\theta_{20}\ge
\frac{(20\pi)^2}{2199}(1-u_0^2/6)^2>149/100.
$$

Both comparisons are checked with $\pi>157/50$. The inequalities persist to the midpoint by monotonicity of sine, and reciprocity gives the reflected middle interval. At each integer phase $20\le j\le n-20$, $F_n$ has sign $(-1)^j$. Every central old root satisfies the strict lag inequality. Exactly 19 old roots on each side must still be located, since the middle samples give $n-40$ distinct roots and the old degree is $n-2$.

## The exact prefixes and rational-ball tail

Use the insertion recurrence for $E_{n,k}$. Write

$$
I=t(1-t)E_{n,k}' + ntE_{n,k},
\qquad
J=\binom n{k-1}(tA_{k-1})E_{n+1-k,k}.
$$

The two next pencils after division by $t$ are $(I+J)/t$ and $(I-J)/t$. These formulas hold through $n=4k-1$, including the four-cycle contribution in the positive pencil at $n+1=4k$. Each term can be computed modulo $t^{49}$, since differentiation is followed by multiplication by $t$. The checker computes the first 48 coefficients of the old polynomial and both pencils using exact integer polynomial arithmetic. A separate reconstruction from cycle contributions checks the positive rows and all their prefixes.

For every $p\ge1$, the run-word representation gives $[t^p]E_{N,k}\le p^N$. The coefficients of both $I$ and $J$ are nonnegative. For $I$ this follows directly since the two contributions from a monomial $t^p$ in $E_{n,k}$ are $p t^p$ and $(n-p)t^{p+1}$. Therefore the absolute coefficients of $I-J$ are bounded by those of $I+J=E_{n+1,k}$, and for any of the three polynomials after division by $t$, the omitted term from an $E$ exponent $p\ge49$ has absolute value at most $p^{n+1}x^{p-1}$ at $t=-x$. Thus the common absolute tail bound is

$$
\frac{x^{48}49^{n+1}}{1-x(50/49)^{n+1}}
$$

whenever the denominator is positive. The consecutive term ratios in the majorant decrease with $p$. The checker supplies a rigorous Arb ball for $x=\exp(-\pi\cot(\pi a/n))$ at each rational angular index $a$. It verifies positivity of the tail denominator in Arb, evaluates the truncated polynomial in Arb, and accepts a sign only when the entire value ball lies beyond the corresponding positive or negative tail enclosure. At $a=0$ the argument is exactly zero and the tail vanishes. No floating-point approximation is used as a sign oracle.

## Brackets and degree exhaustion

For ranks $h=1,\ldots,19$ the checker verifies sign $(-1)^h$ for the old $P_n$ at angular index $a=h+1$. Together with its sign at zero this gives 19 disjoint old root brackets, ending at $a=20$. The middle and reciprocal counts exhaust the old degree, so these brackets each contain one old root and every old root is simple.

In each exterior bracket, bisect in the angular index on the grid with spacing $2^{-24}$. Exact old endpoint signs remain opposite. The checker accepts the refined bracket only once both pencil signs equal $(-1)^h$ at both endpoints and the bracket is strictly separated from the preceding one. These pencil signs also alternate with the signs at the actual old roots in the middle interval, where the strict analytic lag inequality applies. Consequently each pencil has one root in each gap between old brackets or middle old roots. The positive constant and leading coefficients give the two outside roots. Reciprocity makes the two exterior checks identical up to the known parity sign. This exhausts the next degree $n-1$, so neither pencil has a zero inside any exterior old bracket. Its sign at the enclosed old root is therefore the certified endpoint sign. This gives the strict lag inequality at all old roots and strict consecutive interlacing for both pencils.

The recorded replay used Python 3.12.16, python-flint 0.9.0 and FLINT 3.6.0 with 160-bit Arb working precision. The default covers all eligible pairs. Shards may use mutually disjoint ranges of $k$.

~~~sh
python3 check-three-cycle-exterior.py
python3 check-exterior-prefix-agreement.py
~~~

The exported records give the pair count at each threshold, cumulative counts, subdivision totals, and a SHA-256 digest over every final bracket index. The default range is $49\le k\le733$. Exact full-degree sign transfer handles $n<192$ in a separate check. The analytic cutoff handles $n\ge2200$.

[Prefix and sign checker](check-three-cycle-exterior.py) · [Independent prefix comparison](check-exterior-prefix-agreement.py) · [Cycle enumeration](three_cycle_prefix.py) · [Analytic middle proof](three-cycle-2200.md)
