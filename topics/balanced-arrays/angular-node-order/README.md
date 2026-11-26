# Strict ordering of the angular test points

**Supporting theorem.** Let $`n\ge d\ge2`$ and $`1\le r<d`$. Put $`\theta=\pi/d`$, $`\nu=(d-1)/2`$, and define $`H(z)=\sum_{s=0}^r\binom ds z^s`$ and $`B(z)=\sum_{s=0}^{r-1}\binom{d-2}s z^s`$. For $`w>0`$ the phase

$$
\Psi(w)=(n+\nu)\arg H(we^{i\theta})-\nu\arg B(we^{i\theta})-\nu\theta
$$

is strictly increasing, with limits $`-\nu\theta`$ and $`nr\theta`$ at zero and infinity. For every internal quota $`1\le k<\lfloor nr/d\rfloor`$ there is exactly one positive solution of $`\Psi(w_k)=k\pi`$. The radii $`w_k^d`$ therefore increase strictly. This also characterizes the endpoint-adjacent solutions for every integer strictly between the limiting phases divided by $`\pi`$. The arguments start at zero and are continued along the positive real tilt.

The phase comes from the principal term of the Fourier integral for Alexandersson’s balanced-array polynomial. Its determinant uses $`a(t)=\mathbb E[q_Se^{itS}]/\mathbb E[e^{itS}]`$, where $`q_s=s(d-s)/(d(d-1))`$. The identity $`q_s\binom ds=\binom{d-2}{s-1}`$ gives exactly $`a(\theta)=we^{i\theta}B(we^{i\theta})/H(we^{i\theta})`$. Strict ordering removes a possible obstruction to using these test points at every finite height in this range. Establishing the prescribed sign at every radius and height remains open. The geometric test point can give the opposite sign at quadratic aspect. [Conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Sign reversal at geometric test points](../effective-sublinear/square-phase.md)

**Formal verification**　⬜ None. The analytic comparison and the finite certificates have an independent agent-assisted review. [Review and independent replay](ordered-phase-variance-review.md)

## Proof

For a positive binomial row of size $`S`$ conditioned on $`S\le r`$, put $`V=\mathrm{Var}(S)`$. The law reweighted by $`q_S`$ is a translated capped binomial on $`d-2`$ trials; a point mass contributes zero phase derivative. If $`F`$ is either row polynomial, $`\phi(t)`$ its normalized characteristic and $`V_F`$ the variance, then, for $`D=w\,\mathrm d/\mathrm dw`$ and independent copies $`S,S'`$ of that row size,

$$
D\arg F(we^{i\theta})=\frac{\mathbb E[(S-S')\sin(\theta(S-S'))]}{2|\phi(\theta)|^2}.
$$

For the original row law this is strictly positive because every nonzero difference is smaller than $`d`$ and its support includes two consecutive sizes. It suffices to prove the phase derivative positive at $`n=d`$.

For $`d\ge36`$, the [fourth-moment estimate](ordered-phase-fourth.md) compares both angular derivatives with $`\theta V_F`$. The [variance comparison](ordered-phase-weighted.md) separates the two real variances uniformly over all tilts. At mean at most $`d/2`$ the weighted variance is at most $`2V`$ by two cell conditionings. Above mean $`d/2`$, write $`h=d-\mathbb ES`$. The third central moment of the hole count is at most $`(2h-1)V`$, by the one-sided bound on the increments of its discrete Stein kernel. Substitution in the quadratic reweighting formula shows that the variance ratio is at most $`1+\frac{d}{d-1}\frac{d-2h}{d-h}(2-1/h)`$. The [numerical comparison](ordered-phase-variance-review.md) shows the strict inequality $`(3d-1)D\arg H>(d-1)D\arg B`$ in both cases.

For $`2\le d\le35`$, write $`L_F=|F|^2`$ and $`K_F=\Im(zF'\overline F)`$ on the same ray. The positive denominators can be cleared. Two independent exact integer interval computations prove that every interior coefficient in $`2K_HL_B-K_BL_H`$ is positive. The endpoint coefficients vanish. This stronger inequality proves the required one since $`D\arg H>0`$. The computations cover all 595 proper cap–dimension pairs in the remaining range. [Coefficient formulas and certificate](ordered-phase-algebra.md) · [Independent Chebyshev verification](verify-phase-order-chebyshev.py)

Finally both polynomials sum terms in sectors of width strictly less than $`\pi`$. Their continuous arguments range from zero at the origin to their respective degree times $`\theta`$ at infinity. The limits of $`\Psi`$ follow, and the intermediate value theorem and strict increase give existence, uniqueness and ordering. $`\square`$

## Reproduction

From this directory run the following commands with Python 3.

~~~sh
python3 -IB verify-phase-order.py --max-d 35
python3 -IB verify-phase-order-chebyshev.py
~~~

Both checks certify 26,775 positive coefficients and 1,190 zero endpoints. The first verifier also ran through dimension 128 and checked 1,373,632 positive coefficients across 8,128 cap–dimension pairs. The proof uses only dimensions through 35 in its finite step.

## Polynomial signs at sampled radii

The [sample ledger](screen-angular-signs.jsonl.gz) records exact coefficient vectors and 9,162 dyadic samples over 745 parameter triples. The samples were selected by binary64 bisection for the angular phase. At every stored rational tilt the exact polynomial evaluation had the prescribed sign. This experiment leaves the signs at the exact phase radii unresolved. All internal quotas were sampled for ranks one and corank one, with $2\le n\le48$ and $2\le d\le\min(n,10)$, and for the additional vectors in the 36-row ledger. [Screen and exact replay](screen-angular-signs.py) · [36-row coefficient source](../finite-36/exact-vectors.jsonl)

~~~sh
python3 -IB screen-angular-signs.py verify screen-angular-signs.jsonl.gz --finite-vectors ../finite-36/exact-vectors.jsonl
~~~

## Signs near the two quota edges

For fixed dimension and proper cap, every fixed positive deficit from the
top quota has the prescribed sign at its exact angular radius once the
height is large enough. At a fixed bottom quota the signed value converges
to a hyper-Bessel evaluation. Only finitely many dimension–quota pairs
can fail strict positivity of that limit, with no explicit cutoff.
The all-height sign problem remains open. **⬜ None.**
[Edge proofs and independent reviews](edges/README.md)
