# A supplementary-box interpolation can lose real-rootedness

Let $`W_m(t)`$ count assignments of the $`n`$ labeled elements to $`m`$ labeled boxes, with one factor of $`t`$ per box containing at least $`j`$ elements. If $`O_{n,j}^{(r)}(t)`$ concerns ordered partitions with exactly $`r`$ blocks, selecting the occupied box labels gives

$$
W_m(t)=\sum_{r=0}^m\binom mr O_{n,j}^{(r)}(t),\qquad
O_{n,j}(t)=\frac12\sum_{m\ge0}2^{-m}W_m(t).
$$

The second equality uses $`\sum_{m\ge r}2^{-m}\binom mr=2`$. The normalized finite prefix is $`C_m=\sum_{b=0}^m 2^{m-b}W_b`$, so $`C_{m+1}=2C_m+W_{m+1}`$. An argument that maintains real-rootedness through every partial addition $`2C_m+\theta W_{m+1}`$ would imply real-rootedness of the geometric limit. This sufficient closure fails at $`m=2`$.

## Exact discriminant

Fix $`n=2j`$, $`j\ge2`$. The zero-box row vanishes and $`W_1=t`$, so $`C_2=2W_1+W_2`$. Put

$$
C=\binom{2j}{j},\qquad T=\sum_{r=j}^{2j}\binom{2j}{r}2^{2j-r},\qquad A=9^j-3T+3C.
$$

With two boxes at least one is large, and both are large in exactly the $`C`$ balanced assignments. With three boxes, there are $`T`$ assignments in which a specified box is large and $`C`$ in which two specified boxes are large. There is no assignment with three large boxes. It follows that

$$
W_2=(4^j-C)t+Ct^2,\qquad W_3=A+(3T-6C)t+3Ct^2.
$$

Let $`F_\theta=2C_2+\theta W_3`$. Both endpoints $`F_0,F_1`$ have strictly positive discriminant for every $`j\ge2`$. But at $`\theta=2^{-j}`$ the discriminant is strictly negative exactly when $`j\ge16`$. At the first such threshold the primitive polynomial, listed by ascending coefficient, is

$$
[547901605735920,\ 231159571069429,\ 26262204039750].
$$

Its discriminant is $`-4121667757171163267992893959`$. Two counters compare the exact coefficients through threshold 128. One uses the formulas above, and the other independently sums the multinomial weights over every box-size vector. [Checker](verify-collision.py) · [Exact cases](collisions.jsonl.gz) · [Output](collision-output.txt)

For the remaining thresholds, consecutive summands of $`T`$ have ratio at most $`1/2`$, so $`T\le2C2^j`$. The central binomial coefficient satisfies $`4^j/(2j+1)\le C\le4^j`$. Hence $`A\ge9^j/2`$ whenever $`12\cdot8^j\le9^j`$. The linear coefficient of $`F_{2^{-j}}`$ is bounded by $`4+2\cdot4^j+6C\le9\cdot4^j`$. The quadratic coefficient is at least $`2C`$. The constant-quadratic product times four exceeds the squared linear coefficient once

$$
4(9/8)^j>81(2j+1).
$$

At the other endpoint $`T\ge C2^j`$, so the linear coefficient of $`F_1`$ is at least $`3C(2^j-2)\ge(3/2)C2^j`$. The constant coefficient is at most $`9^j`$, and the quadratic coefficient is $`5C`$. Thus its discriminant is positive whenever $`9\cdot16^j\gt 80(2j+1)9^j`$. The verified inequalities at $`j=128`$ persist by comparing successive ratios. In particular $`(2j+3)/(2j+1)\lt 9/8\lt 16/9`$ for all $`j\ge128`$. The $`F_0`$ claim also follows directly from its zero constant and positive linear coefficient.

## Asymptotic collision parameters

Let $`\theta_-\lt \theta_+`$ be the two positive zeros of the discriminant as a function of $`\theta`$, for large $`j`$. For fixed $`r\ge0`$, the ratio of the $`(j+r)`$th summand of $`T`$ to the first tends to $`2^{-r}`$, and the same geometric sequence dominates all these ratios. Thus $`T\sim2C2^j`$, while $`C\sim4^j/\sqrt{\pi j}`$ and $`A\sim9^j`$.

Putting $`L=4+2(4^j-C)`$ and $`M=3T-6C`$, the discriminant has the exact quadratic expression

$$
L^2+(2LM-8CA)\theta+(M^2-12CA)\theta^2.
$$

Its coefficients are asymptotic to $`4\cdot16^j`$, $`-8C9^j`$ and $`36C^2 4^j`$, respectively. The product of the constant and quadratic coefficients divided by the square of the linear coefficient tends to zero, since it is asymptotic to $`(9/4)(64/81)^j`$. Consequently the smaller zero is asymptotic to the constant divided by the negative linear coefficient, and the larger to the negative linear coefficient divided by the quadratic coefficient. This gives

$$
\theta_-\sim\tfrac12\sqrt{\pi j}(4/9)^j,\qquad
\theta_+\sim\tfrac29\sqrt{\pi j}(9/16)^j.
$$

## Finite auxiliary grid

The [finite ledger](medium.jsonl.gz) records the exact $`W_m,C_m`$ coefficients for $`j\in\{2,3,4,5,6,7,8,9,10,12,15\}`$, $`1\le m\le32`$ and $`0\le n\le65`$. These are 23,232 pairs of coefficient rows. Each threshold has 2,112 rows for each reality check, 2,080 consecutive-size comparisons for each sequence, and 2,046 comparisons between successive box prefixes and between the previous prefix and the last summand. The earlier $`1\le m\le16`$, $`0\le n\le32`$, $`2\le j\le8`$ grid is wholly contained and its 3,696 records agree exactly. [Medium summary](medium-summary.jsonl) · [Small summary](small-summary.jsonl) · [Replay script](search.py)

Both families were real-rooted and weakly interlaced in consecutive size throughout this grid. The tests permit repeated roots and do not identify the direction. Comparisons as the number of boxes varies fail in the recorded instances. The real-rootedness check uses Sturm counts on the squarefree part. The weak interlacing check cancels the common factor and tests alternating order in either direction by the signed remainder index. These finite facts make no claim about larger sizes or thresholds or about the strict direction in the original conjecture.
