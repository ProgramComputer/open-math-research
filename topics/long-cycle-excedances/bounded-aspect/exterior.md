# Uniform bounded-aspect exterior signs from old size 1,000

Let $`E_{n,k}(t)`$ count excedances over permutations with minimum cycle length $`k`$, and put $`P_n=E_{n,k}/t`$. Suppose $`1000\le n<10{,}000`$ and $`4\le n/k\le20`$. With $`H=\lfloor7\sqrt n/20\rfloor`$, the first $`H`$ nonzero old roots by increasing modulus are simple and negative. The sign of the actual next $`P_{n+1}`$ at rank $`h`$ is $`(-1)^h`$. The new root of rank $`h`$ lies before the old rank-$`h`$ root, and every higher new rank lies after it in modulus. The old exterior roots precede the integer middle sample at $`(H+1)\pi/n`$ and the common-circle sample at $`(H+5/6)\pi/n`$. The reciprocal conclusions hold at the opposite end. [Large-aspect exterior proof](../aspect-20/high-exterior/README.md)

## Coefficient bounds at the front

Use the ordinary run-color coefficients $`\alpha_{N,p}=[t^p]E_{N,k}/p^N`$. If $`f(N,p,k)`$ is the acceptance probability of the minimum-size condition on cycles of the color permutation, then $`0\le f(N,p,k)-\alpha_{N,p}\le2p e^{-\lfloor N/2\rfloor/p}`$. Each color appearing in both label halves suffices for the run boundaries. Adopt the encoding and append-one-label coupling from the [effective exterior theorem](../effective-front.md).

Here $`1000\le N\le10{,}000`$ and $`4\le N/k\le21`$, which covers both the old and next rows. Write $`v=\sqrt N`$, $`a=kp/N`$, and $`J=\lfloor v/2\rfloor`$. The following estimates suffice:

$$
\begin{aligned}
\alpha_{N,p}&\ge\frac{.99}{1+(8/3)a}&&\text{for }p\le\lfloor.35v\rfloor+1,\\
\alpha_{N,p}&\le\min(1,1.52/a)&&\text{for }p\le J.
\end{aligned}
$$

For the lower bound the case $`p=1`$ is exact. Otherwise condition the run permutation to have no cycle shorter than $`b=\lceil 4a/3\rceil`$. This has probability $`d(p,b)\ge1/(2b-1)`$. A $`j`$-cycle with $`j\ge b`$ receives a binomial number of labels with mean $`jN/p\ge4k/3`$. Its probability of receiving fewer than $`k`$ labels is at most $`e^{-jN/(32p)}<e^{-2.55j}`$, using $`p\le .382v`$. For $`j<p`$ the conditional mean number of $`j`$-cycles is at most $`2/j`$, because the residual probability $`d(p-j,b)`$ is at most $`1/b`$ when nonzero. The full cycle always succeeds. If $`b\ge2`$, the total relative loss is bounded by $`\sum_{j\ge2}e^{-2.55j}`$ plus the relative word cost $`4p^2e^{-\lfloor N/2\rfloor/p}\le N e^{-(N-1)/v}`$. This is below $`.01`$, giving the lower bound. If $`b=1`$ the count of $`j`$-cycles has mean $`1/j`$, so using the geometric sum from $`j=1`$ gives $`\alpha_{N,p}>.90`$. This also suffices because $`a\ge2/21`$.

For the upper bound at $`p\le J`$, only $`a>3/2`$ requires work. Compare against $`b=\lceil2a/3\rceil`$. Any accepting color permutation with a shorter cycle must supply at least $`k`$ labels to a binomial mean below $`2k/3`$. Its probability is at most $`e^{-k/15}`$ by the moment generating function at $`\log(3/2)`$. Sum the expected counts $`1/j`$ of these shorter cycles. Then $`f(N,p,k)\le 1/b+(1+\log p)e^{-k/15}`$. The second term times $`a`$ is bounded by $`(3/2)(1+\log(v/2))e^{-v/5}<.02`$, as $`N/p\ge2v`$ and both maximizations reduce to the smallest admissible $`a`$ and $`v`$. This gives the asserted coefficient upper bound.

In particular, if $`q`$ is a central index at most $`\lfloor.35v\rfloor+1`$ and $`p\le J`$, then

$$
\frac{\alpha_{N,p}}{\alpha_{N,q}}
\le5.12\max(1,q/p).
$$

To obtain this bound, use $`a_q\le a_p\max(1,q/p)`$ and $`(1+(8/3)a_p)\min(1,1.52/a_p)\le1+(8/3)1.52`$.

## Comparing the actual next-row coefficients

At the old size write $`v=\sqrt n`$, $`x=n/k`$, and put $`\delta_p=p(\alpha_{n+1,p}-\alpha_{n,p})`$. Extend both coefficient sequences by zero outside their supports. By appending one uniform color, $`f(n+1,p,k)\ge f(n,p,k)`$, and new acceptance requires a hit to a color cycle with exactly $`k-1`$ labels. As in the large-aspect proof, the mean count $`1/j`$ cancels the hit probability $`j/p`$. With

$$
b(y)=\binom n{k-1}y^{k-1}(1-y)^{n+1-k},
$$

one obtains $`p(f(n+1,p,k)-f(n,p,k))\le\sum_{j=1}^{p-1}b(j/p)`$. For $`p\le J=\lfloor v/2\rfloor`$, put $`\epsilon=n e^{-(n-1)/v}<10^{-6}`$. The total word-boundary contribution to the absolute change on this scale is at most $`\epsilon`$. Thus

$$
-\epsilon\le\delta_p\le .47/\sqrt k+p/(n+1)+\epsilon .
$$

In detail, $`b`$ is unimodal and its sampled sum is at most its maximum plus $`p`$ times its beta integral $`1/(n+1)`$. Since $`k\ge50`$ and $`(k-1)/n\le1/4`$, Stirling's bounds give
$`\max b\le e^{1/(12n)}/\sqrt{2\pi(k-1)(1-(k-1)/n)}<.47/\sqrt k`$.

If $`q`$ is any central index, multiplying the bound by $`1/\alpha_{n,q}\le(1+(8/3)(.382)v/x)/.99`$ gives

$$
-.001<\frac{\delta_p}{\alpha_{n,q}}<.46
\qquad(p\le J).
$$

Indeed use $`q\le .382v`$, $`p/(n+1)\le1/(2v)`$, $`4\le x\le20`$, $`31.25\le v\le100`$, and $`1/\sqrt k=\sqrt x/v`$. The upper bound uses the sum
$`.47(\sqrt{20}/31.25+(8/3)(.382)/2)+1/(2\cdot31.25)+(8/3)(.382)/8+\epsilon(1+(8/3)(.382)100/4)`$ before division by $`.99`$. The stronger lower bound exploits the direction of the append coupling.

## Root isolation and signs

Fix $`1\le h\le H`$. Use $`\rho=\alpha_{n,h}/\alpha_{n,h+1}`$, $`u=\rho(h/(h+1))^n`$, and the normalized old row $`F(z)=E_{n,k}(uz)/(\alpha_{n,h}h^n(uz)^h)`$. Its central terms are $`1,z`$. The consecutive outward ratios of the pure monomial bases are bounded by $`q_0=e^{-n/(h+1)^2}`$. In particular $`q_0\max(\rho,\rho^{-1})<1/150`$: for $`h\ge6`$ the coefficient ratios are below 6 and $`h+1\le .382\sqrt n`$, and for $`h\le5`$ the ratios are below 11 and $`q_0\le e^{-1000/36}`$.

At offset $`l\ge1`$ from the central pair the left coefficient ratio to its central term is at most $`5.12(l+1)`$. The right local ratio for $`p=h+1+l\le J`$ is at most $`5.12`$. For $`p>J`$ one has $`l\ge4`$, $`p<5l`$, and $`1/\alpha_{n,h+1}<3(l+1)`$. These follow from $`l>(.15)\sqrt n-1`$ and the lower bound on the central coefficient. Thus with $`s=(1/150)\max(r_+,1/r_-)`$ at $`r_-\le |z|\le r_+`$, the left tail is at most $`5.12\sum_{l\ge1}(l+1)s^l`$. The right tail is at most $`r_+(5.12\sum_{l\ge1}s^l+3\sum_{l\ge4}(l+1)s^l)`$. They give a combined bound below $`.15`$ on $`|z+1|=.15`$. For each outer circle use the simpler bound $`5.12(1+|z|)\sum_{l\ge1}(l+1)s^l`$, which is below $`1/2`$ at $`|z|=1/2`$ and below 2 at $`|z|=3`$. Rouché for $`z^{h-1}F`$ gives one real simple negative root in the disk about $`-1`$ and respectively $`h-1`$ and $`h`$ roots in the smaller and larger circles. This fixes the absolute rank after scaling. The same estimates hold with the next row's own adjacent balance $`u_{n+1}`$ and the same $`h`$.

At the actual old root $`t=uz`$ use

$$
\frac{E_{n+1,k}(t)-hE_{n,k}(t)}{\alpha_{n,h}h^n t^h}
=\sum_{p\ge1}\frac{p^n t^p}{\alpha_{n,h}h^n t^h}\bigl((p-h)\alpha_{n,p}+\delta_p\bigr).
$$

The weighted old terms have central contribution $`z<-.85`$. The two central coefficient changes have normalized total at most $`.46+1.15(.001)`$ from the directional bounds above, since $`z<0`$. On this disk $`s<1/125`$. The old weighted tails are bounded by

$$
5.12\sum_{l\ge1}l(l+1)s^l
+1.15\left(5.12\sum_{l\ge1}(l+1)s^l+3\sum_{l\ge4}(l+1)^2s^l\right)<.19 .
$$

The noncentral local changes contribute at most $`.46(1+1.15)s/(1-s)<.008`$. The far changes contribute at most $`1.15\sum_{l\ge4}15l(l+1)s^l<.001`$, using $`|\delta_p|\le p`$. Hence the actual next scaled value is strictly negative. Restoring the sign of $`t^h`$ and dividing by $`t`$ gives $`(-1)^h`$ for $`P_{n+1}`$.

For $`p\ge2`$ central, $`\alpha_{n+1,p}/\alpha_{n,p}`$ lies in $`[.77,1.23]`$, and at $`p=1`$ it is one. The old root therefore has $`|t|/u_{n+1}`$ in $`(1/2,3)`$, since the ratio of the balances contains the factor $`(h+1)/h`$ and $`|t|/u\in(.85,1.15)`$. When $`h=1`$ use $`p=1`$ exactly in this comparison. The next row has sign $`(-1)^{h-1}`$ at $`-u_{n+1}/2`$ by its bound at $`|z|=1/2`$. The sign at the old root places it after the unique rank-$`h`$ new root and before all higher new ranks.

## Join and scalar replay

At $`h=H\ge6`$ the old modulus is below $`7(H/(H+1))^n`$. The bound

$$
n\left(\log(1+1/H)-\frac1{H+5/6}\right) >\frac{n}{3(H+1)^2}\ge\frac1{3(.382)^2}>\log7
$$

follows from the convex midpoint estimate on the integral of $`1/(H+y)`$, and $`\pi\cot((H+5/6)\pi/n)<n/(H+5/6)`$. Thus the front lies before this phase sample, hence also before the integer sample at $`(H+1)\pi/n`$. As in the large-aspect proof, $`n\sin^2((H+5/6)\pi/n)>1`$ and $`n\sin^2((H+1)\pi/n)>6/5`$. Reciprocity gives the other end.

Run `python3 -I -B check-exterior.py` for the exact rational scalar checks. The proof supplies the exterior roots and actual next signs on this whole aspect range. The middle proof is a separate input. Formal verification is ⬜ None. [Checker output](exterior-output.txt)
