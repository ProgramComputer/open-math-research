# Independent review of the nine-column pure flag obstruction

**Verdict.** The same pure flag family in every row, with unit cell weights, gives non-log-concave balanced-quota coefficients for $`n=7t`$ and all sufficiently large integers $`t`$. The example uses nine columns throughout and lies outside the uniform row-cap conjecture.

Take the clique complex of the disjoint union of a triangle and a wheel with five rim vertices. The triangle supplies three ordinary columns. The wheel supplies five special rim columns and a guard column $`z`$ adjacent to all five rim vertices. The only two-element rim faces are cycle edges. Every maximal clique has size three, either the ordinary triangle or the guard with a rim edge. This proves purity and the flag property together. A maximal-size row cap would allow any pair, including pairs meeting both components.

Fix $`j\in\{0,1,2\}`$ and set $`k=2t-j`$. Let $`s`$ be the number of rows with nonempty rim support. Let $`u_v`$ count singleton rim rows at vertex $`v`$, $`w_v`$ count rim-edge rows on edge $`(v,v+1)`$, and $`p=\sum_v u_v`$. Then

$$
w_{v-1}+w_v=k-u_v,\qquad p=2s-5k.
$$

Each ordinary column requires $`k`$ of the $`7t-s`$ rim-empty rows. Consequently, for $`i=s-\lceil5k/2\rceil`$ the only possible offsets are $`0\le i\le B_j=\lfloor7j/2\rfloor`$. We have $`p=2i+h_j`$ with $`h_j=j\bmod 2`$. In particular the number of singleton vectors to sum over is bounded independently of $`t`$. For each vector the odd cycle equations have at most one solution, with $`w_v=t+O(1)`$. More explicitly, $`2w_v`$ is an alternating sum of five right-hand sides. Its parity is that of $`5k-p`$, which is even, so the solution is integral. Since each right-hand side is $`2t+O(1)`$, the solution is positive for sufficiently large $`t`$. The $`i=0`$ term exists by taking all $`u_v=0`$ for $`j`$ even, or taking exactly one singleton for $`j=1`$.

For a fixed feasible singleton vector, the number of choices of the rim supports is

$$
\frac{(7t)!}{(7t-s)!\prod_v w_v!\prod_v u_v!}.
$$

Divide this expression by $`H_t=(7t)!/((2t)!(t!)^5)`$. Since $`7t-s=2t+O(1)`$ and all $`w_v=t+O(1)`$, fixed factorial shifts give a ratio of order $`t^{p}`$: the sum of the denominator shifts is $`(7t-s-2t)+\sum_v(w_v-t)=-p`$. The ordinary columns independently choose their $`k`$ rows, contributing $`\binom{7t-s}{k}^3`$ of order $`t^{3(B_j-i)}`$. Once those choices are made, the guard may occupy any $`k`$ rows with no ordinary cell. At least the $`s`$ rim-occupied rows qualify, and at least $`k`$ rows contain an ordinary cell. Thus the number of guard choices lies between $`\binom{s}{k}`$ and $`\binom{7t-k}{k}`$, both comparable to $`G_t=\binom{5t}{2t}`$ by fixed factorial shifts. Rim supports, ordinary supports and guard supports reconstruct the full array uniquely.

After removing the common factor $`H_tG_t`$, the contribution of a fixed feasible singleton vector is therefore of order $`t^{h_j+3B_j-i}`$. All contributions are nonnegative and their number is bounded, with the largest exponent attained at $`i=0`$. In order $`j=0,1,2`$, the coefficient exponents are $`0,10,21`$. In particular

$$
\frac{a_{2t-2}a_{2t}}{a_{2t-1}^2}=\Theta(t),
$$

so the ratio strictly exceeds one eventually. The coefficients count arrays and are nonnegative. Newton's inequalities rule out real-rootedness.

**Signed** — four_literature, independent agent-assisted mathematical review.
