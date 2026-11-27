# Consecutive ordered-partition signs with a quadratic old row

**Theorem.** At every threshold $`j\ge2`$, all consecutive pairs of the unweighted ordered large-block polynomials with quadratic old row strictly interlace in the prescribed direction. This covers $`2j\le n\le3j-1`$. The last pair, from $`3j-1`$ to $`3j`$, includes the first cubic row. In increasing modulus, the order starts with the smallest new root, then the smallest old root, then the second new root and second old root. At the first cubic row the additional new root comes last. The argument and finite checks passed independent review. Formal verification is ⬜ None. [Alexandersson’s conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/1) · [Earlier linear-old-row proof](../first-degree-increase/README.md)

Together with the linked linear-old theorem, consecutive interlacing holds for every old size $j\le n\le3j-1$.

## A sign separator from the coefficient differences

Write $`q_n(t)=O_{n,j}(t)/n!`$ and $`A(z)=(2-e^z)^{-1}`$. For the marked block series $`B_j(z)=\sum_{\ell\ge j}z^\ell/\ell!`$, the coefficient of $`(t-1)^k`$ in $`q_n(t)`$ is $`[z^n]B_j^k A^{k+1}`$ by the original reciprocal generating function. Put $`\lambda=\log2`$, $`s=n-2j`$, and $`m=n-j=j+s`$. Define

$$
 a_n^{\ast}=2\lambda^{n+1}[z^n]A,
 \qquad C_r^{\ast}=4\lambda^{r+2}[z^r]A^2,
 \qquad E_r^{\ast}=8\lambda^{r+3}[z^r]A^3.
$$

Let $`u_\ell=\lambda^\ell j!/(j+\ell)!`$, $`U=\sum_{\ell\ge0}u_\ell`$, and $`w_\ell=\sum_{i=0}^\ell u_i u_{\ell-i}`$. Then $`\sum w_\ell=U^2`$. Set

$$
 B_m^{\ast}=\sum_{\ell=0}^m u_\ell C_{m-\ell}^{\ast},
 \qquad D_s^{\ast}=\sum_{\ell=0}^s w_\ell E_{s-\ell}^{\ast}.
$$

At the common coordinate $`y=\lambda^{j-1}(1-t)/(2j!)`$, multiplication of $`q_n(t)`$ by $`2\lambda^{n+1}`$ gives

$$
 P(y)=a-b y+d y^2,\qquad (a,b,d)=(a_n^{\ast},B_m^{\ast},D_s^{\ast}).
$$

For the next row write $`(a',b',d')=(a_{n+1}^{\ast},B_{m+1}^{\ast},D_{s+1}^{\ast})`$. Put $`v=a'/a`$, $`\Delta b=b'-v b`$, and $`\Delta d=d'-v d`$. If the next row is quadratic, subtracting $`vP`$ from its normalized polynomial gives exactly $`y(\Delta d y-\Delta b)`$. Thus if $`\Delta b,\Delta d>0`$, the signs at the old roots are in the desired directions provided that

$$
 b>a\frac{\Delta d}{\Delta b}+d\frac{\Delta b}{\Delta d}.
 \tag{1}
$$

Indeed (1) is exactly $`P(y_*)<0`$ for $`y_*=\Delta b/\Delta d`$. Since $`d>0`$, the old quadratic has two distinct real roots $`y_1<y_*<y_2`$. Both correspond to strictly negative $`t`$ because $`q_n`$ has positive constant and nonnegative coefficients. In particular both $`y_i`$ are positive. The new values at $`y_1,y_2`$ are strictly negative and positive, respectively. The value at $`t=0`$ is positive, so there is a new root before $`y_1`$ and one between the old roots. These exhaust the degree. At a degree increase the cubic perturbation to this comparison will be treated below.

## Coefficient estimates uniform in the quadratic band

Use $`\mu=7/20`$. The simple and double poles give the estimates

$$
 a_n^{\ast}=1+\epsilon_n,\quad |\epsilon_n|\le14\mu^n,
 \qquad C_r^{\ast}=r+1+\lambda+\eta_r,\quad |\eta_r|\le196\mu^r.
$$

On $`|z|=2`$, put $`x=z-\lambda=a_0+ib_0`$. Then $`|x|>13/10`$, $`a_0>-3`$ and $`|b_0|\le2`$. The identity $`|1-e^x|^2=(1-e^{a_0})^2+2e^{a_0}(1-\cos b_0)`$, the lower bounds $`|1-e^{a_0}|\ge e^{-3}|a_0|`$ and $`1-\cos b_0\ge2b_0^2/\pi^2`$, and $`4e^3>\pi^2`$ imply $`|1-e^x|\ge e^{-3}|x|`$. Hence $`|A(z)|<9`$ using $`e^3<21`$. The principal parts of $`A`$ and $`A^2`$ are $`-1/(2x)`$ and $`1/(4x^2)-1/(4x)`$. Their analytic remainders on this circle are bounded by 10 and 100. Cauchy gives the displayed errors using $`\lambda<7/10`$. The other poles lie outside the circle.

For the triple pole, keep $`x=z-\lambda`$. The principal part of $`A(z)^3`$ is $`-1/(8x^3)+3/(16x^2)-1/(8x)`$ by cubing $`A=-1/(2x)+1/4-x/24+O(x^3)`$. The same circle bounds give a pole-subtracted remainder of modulus below $`800`$. Cauchy's estimate gives

$$
 E_r^{\ast}=\frac{(r+1)(r+2)}2+\frac{3\lambda}{2}(r+1)+\lambda^2+\eta^{(3)}_r,
 \qquad |\eta^{(3)}_r|\le2200\mu^r.
$$

It follows for every $`r\ge0`$ that

$$
 0<E_r^{\ast}\le\frac{(r+4)^2}{2},\qquad r+2\le E_{r+1}^{\ast}-E_r^{\ast}\le r+4.
 \tag{2}
$$

For $`r\ge8`$, the first-difference error is at most $`2200(1+\mu)\mu^8<19/20`$, and the polynomial part has first difference $`r+2+3\lambda/2`$. The additive error for the value bound is at most $`2200\mu^8<1`$, which is smaller than the margin to $`(r+4)^2/2`$. For $`r<8`$, the checker bounds the exact coefficients using $`693147/10^6<\lambda<693148/10^6`$ from the positive series for $`\log2`$ with ratio $`1/3`$.

Suppose now $`j\ge20`$ and $`0\le s\le j-1`$. Let $`\gamma=1/30`$. Since $`u_\ell\le\gamma^\ell`$ we have $`1\le U\le(1-\gamma)^{-1}`$ and

$$
 \frac{1}{U^2}\sum_{\ell\ge0}\ell w_\ell
 \le \frac{2\gamma}{(1-\gamma)^2}.
$$

The required bounds are

$$
 \frac bU\ge j+s,
 \qquad \frac{49}{50}\le\frac{\Delta b}{U}\le\frac{51}{50},
 \qquad s+\frac32\le\frac{\Delta d}{U^2}\le s+5,
 \qquad \frac{d}{U^2}\le\frac{(s+4)^2}{2},
 \qquad a\le\frac{101}{100}.
 \tag{3}
$$

To check the first bound, retain just $`u_0=1`$ in $`b`$. For $`m=j+s\ge20`$, $`C_m^{\ast}\ge m+1+\lambda-1/20`$. Dividing by $`U`$ loses at most $`\lambda(m+2)/(j+1)<7/5`$ since $`U\le(1-\lambda/(j+1))^{-1}`$ and $`m\le2j-1`$. The additive gain $`1+\lambda-1/20`$ is larger. We also have the crude upper bound $`b/U\le m+198`$ from the $`C_r^{\ast}`$ bound.

For the raw first difference in $`B_m^{\ast}`$, compare

$$
 B_{m+1}^{\ast}-B_m^{\ast}=
 \sum_{\ell=0}^m u_\ell(1+\eta_{m+1-\ell}-\eta_{m-\ell})+u_{m+1}C_0^{\ast}
$$

with $`U`$. Use $`C_0^{\ast}=4\lambda^2<2`$ and bound the tail by $`3\gamma^{m+1}/(1-\gamma)`$. The coefficient errors total at most $`196(1+\mu)\mu^m/(1-\gamma/\mu)`$, and the two bounds sum to less than $`1/100`$ at $`m\ge20`$. Moreover $`|v-1|<30\mu^{2j}`$ from the estimate on $`a_n^{\ast}`$. The correction $`|v-1|b/U`$ is smaller than $`1/100`$ by $`b/U\le2j+198`$. These bounds prove the estimate for $`\Delta b`$. The bound for $`a`$ follows from $`n\ge2j`$.

For $`d`$, summing (2) against $`w_\ell`$ gives its upper bound in (3). The raw first difference is

$$
 D_{s+1}^{\ast}-D_s^{\ast}=
 \sum_{\ell=0}^s w_\ell(E_{s+1-\ell}^{\ast}-E_{s-\ell}^{\ast})+w_{s+1}E_0^{\ast}.
$$

It is at most $`U^2(s+4)`$ by (2) and $`E_0^{\ast}=8\lambda^3<3`$. For a lower bound, use $`E_{s+1-\ell}^{\ast}-E_{s-\ell}^{\ast}\ge s+2-\ell`$. Since $`s+2\le2\ell`$ when $`\ell>s`$, the lost tail in the $`s+2`$ term costs at most $`2\sum\ell w_\ell`$. Hence the raw difference is at least $`U^2(s+2)-3\sum\ell w_\ell > U^2(s+7/4)`$. Finally $`|v-1|d/U^2\le15\mu^{2j}(j+4)^2<1/4`$. This proves the bound for $`\Delta d`$. The products involving $`\mu^{2j}`$ decrease for $`j\ge20`$, so the indicated rational checks at that endpoint suffice.

## Same-degree pairs

Divide the right side of (1) by $`U`$. From (3) it is bounded above by

$$
 \frac{11}{10}(s+5)+\frac{21}{40}\frac{(s+4)^2}{s+3/2}
 \le\frac{13}{8}s+\frac{451}{40},
$$

using $`(s+4)^2/(s+3/2)\le s+11`$. Since $`s\le j-1`$, the difference from the lower bound $`b/U\ge j+s`$ is at least $`3j/8-451/40>0`$ for $`j\ge32`$. This proves both signs for every same-degree pair at these thresholds. For $`2\le j<32`$, the checker reconstructs the original labelled rows by choosing their first block, independently matches the coefficient expansion about $`t=1`$, and tests (1) without numerical roots on all 465 same-degree pairs.

## First cubic row

At the first cubic row, $`n+1=3j`$, the coefficient of $`(t-1)^3`$ is $`(j!)^{-3}`$. Under the same normalization its contribution is $`-e y^3`$ with $`e=16\lambda^4<4`$. Here $`s=j-1`$ in the old row. For $`j\ge64`$ the proof of (1) gives the quantitative margin

$$
 b-a\frac{\Delta d}{\Delta b}-d\frac{\Delta b}{\Delta d}>\frac{jU}{6},
$$

since $`3/8-451/(40\cdot64)>1/6`$. At the smaller old root, adding the negative cubic term preserves the strict negative sign. At the larger old root, $`-P(y_*)=d(y_*-y_1)(y_2-y_*)`$ and $`y_1>0`$. The quantitative margin therefore gives $`y_2-y_*>jU/(6d)`$. By (3), $`\Delta d\ge(j+1/2)U^2`$ and $`d\le U^2(j+3)^2/2`$, so

$$
 \Delta d(y_2-y_*)>\frac{U}{3}\left(\frac{j}{j+3}\right)^2>\frac U4.
$$

On the other hand $`d\ge E_s^{\ast}\ge s^2/2`$ from (2), and $`b/U\le2j+198`$. Thus $`y_2\le b/d<11U/j`$ for $`j\ge64`$. The perturbation after factoring out $`y_2`$ is $`e y_2^2<4(11U/j)^2<U/4`$, since $`U\le30/29`$. The new sign at the farther old root remains positive. The new cubic is positive at $`t=0`$ and negative at infinity in the positive $`y`$ direction, so these two interior signs exhaust three distinct negative roots in the specified order.

For $`2\le j<64`$, the exact checker reduces the new cubic modulo the old quadratic in $`x=1-t`$. The affine remainder has positive slope and its rational zero gives a negative old quadratic value in each of the 62 cases, so the same strict signs and degree count follow. This finishes the entire quadratic-old range.

## Replay

Run `python3 -B check.py` beside this note. The checker uses only the standard library, checks the rational constants in the pole estimates, and recomputes the original integer coefficient rows independently of the marked expansion in every finite case. It certifies 465 equal-degree pairs and 62 first cubic transitions. [Checker](check.py) · [Recorded output](check-output.txt)

[Independent mathematical review](review.md) · [Independent exact sign checker](independent.py) · [Independent checks of the analytic constants](constants.py)
