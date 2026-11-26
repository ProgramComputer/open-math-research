# A half-square-root exterior range for aspects 20 through 100

Let $E_{n,k}(t)$ count excedances of permutations with every cycle of length at least $k$, and $P_n=E_{n,k}/t$. Assume $n\ge10^6$ and $20\le x=n/k\le100$. Put $H=\lfloor\sqrt n/2\rfloor$. The first $H$ old nonzero roots in modulus are simple and negative, and the signs of the actual $P_{n+1}$ at these roots, starting nearest zero, are $(-1)^h$ at rank $h$. These roots are before the first middle sample at phase $(H+1)\pi/n$, where $n\sin^2\theta>49/20$. Reciprocity gives the corresponding conclusions at the far end. The old-to-new comparison below uses the actual next row.

## Appending one run color

For $p\ge1$, let $f(n,p,k)$ be the minimum-size acceptance probability of a uniform word on $p$ colors together with an independent uniform permutation of the colors. Each cycle of the color permutation receives the letters assigned its colors, and acceptance requires every cycle to receive at least $k$ letters. The run-color encoding gives $\alpha_{n,p}=[t^p]E_{n,k}/p^n$ by additionally requiring nonempty colors and ascending boundaries between runs. Every color occurring in both halves of the labels guarantees these boundary conditions. Thus

$$
0\le f(n,p,k)-\alpha_{n,p}\le2p e^{-\lfloor n/2\rfloor/p}.
$$

This is the same run model as in the [effective exterior proof][front]. For the color comparison, begin with $p$ colors. Recolor each letter independently into the new color with probability $1/(p+1)$, maintaining its old color otherwise. Insert the new color into a uniform one of the $p+1$ permutation slots, which include the singleton slot and one slot after each of the old colors. The resulting word and color permutation are independent and uniform for $p+1$ colors.

If old acceptance fails and new acceptance succeeds, insertion must rescue the cycle into which the new color is inserted. The other cycles only shrink. In the singleton case no old cycle can be rescued. For an old $j$-color cycle, its old mass is contained in its new mass when it receives the new color. The probabilities of reaching $k$ are respectively $G(j/p)$ and $G((j+1)/(p+1))$, where $G(b)=\Pr(\mathrm{Bin}(n,b)\ge k)$. Its insertion probability is $j/(p+1)$, and the expected count of $j$-cycles is $1/j$. Since $(j+1)/(p+1)\le(j+1)/p$ and the binomial tail is increasing, summing the rescue probabilities telescopes and gives

$$
f(n,p+1,k)\le f(n,p,k)+\frac1{p+1}.
$$

The $j=p$ difference is zero. This one-sided estimate is uniform in $n,k,p$.

## Local coefficient envelopes

Set $v=\sqrt n$. Work on the local indices $3v/10\le p\le3v/5$, and put $a=p/x\ge3$. Let $d(p,b)$ be the fraction of color permutations on $p$ colors whose cycles all have length at least $b$. The elementary recurrence obtained by distinguishing one cycle gives $1/(2b-1)\le d(p,b)\le1/b$ for $p\ge b$. Use $b_+=\lceil a+1/2\rceil$ and $b_-=\lceil a-1/2\rceil$. Both lie between one and $p$.

For a color cycle of length $j=a+u\ge b_+$, its binomial mean is $nj/p$. The lower-tail Chernoff exponent for failing to reach $k$ is at least

$$
\frac{nx}{2p^2}\frac{a u^2}{a+u}
\ge\frac{250}{21}u
\qquad(u\ge1/2).
$$

This uses $nx/(2p^2)\ge250/9$ and $a u/(a+u)\ge3/7$. Conditional on all color cycles being at least $b_+$, the expected number of $j$-cycles for $j<p$ is $d(p-j,b_+)/(j d(p,b_+))\le2/j$, with zero if the residual length is too small. A full color cycle cannot fail. The union bound is thus at most $2e^{-125/21}/(1-e^{-250/21})$. For $j=a-u<b_-$ the upper-tail Chernoff exponent for reaching $k$ is at least $(nx/(2p^2))u^2\ge(125/9)u$. The upper union bound relative to $d(p,b_-)$ weighs a $j$-cycle by at most $(2b_--1)/j\le2(1+u)$. The decreasing envelope summed at $u=1/2,3/2,\ldots$ bounds this relative error by $1/100$.

The independent word boundary error is negligible on these indices. Indeed $\lfloor n/2\rfloor/p\ge4v/5$ and $4v^3e^{-4v/5}<1/1000$ for $v\ge1000$, using the eighth positive exponential term. This accounts both for the lower relative error against $d(p,b_+)$ and for $p(f-\alpha)$. The exact scalar checks give

$$
\frac{99/100}{2a+2}\le\alpha_{n,p}\le\frac{101/100}{a-1/2}.
$$

For local indices $p,q$ this yields $\alpha_{n,p}/\alpha_{n,q}\le(10/3)\max(1,q/p)$. The one-sided color comparison gives $\alpha_{n,p+1}/\alpha_{n,p}\le9/8$ whenever both indices are local, since the relative increase is at most $(1001/990)2(1/x+1/p)<1/8$.

## Consecutive rows at fixed color count

Appending one letter to the word while keeping the color permutation gives

$$
0\le p(f(n+1,p,k)-f(n,p,k))
\le \lambda_p
=\sum_{j=1}^{p-1}\binom n{k-1}(j/p)^{k-1}(1-j/p)^{m}
 f(m,p-j,k),
\qquad m=n+1-k.
$$

To see this, an accepting append after old failure must hit a color cycle with exactly $k-1$ labels. Its hit probability $j/p$ cancels its mean multiplicity $1/j$ up to the factor $1/p$. Given that count, the other labels and the remaining color permutation are independent uniform among the other colors. This gives the displayed bound.

For $r=p-j$ and $a'=kr/m$, the residual permission probability satisfies $f(m,r,k)\le2/a'$. It is immediate at $a'\le2$. Otherwise require color cycles to have length at least $\lceil2a'/3\rceil$ in the deterministic comparison. The unrestricted count of such color permutations is at most $3/(2a')$. Each smaller color cycle has mean less than $2k/3$ and passes only with probability at most $e^{-k/15}$. The expected number of color cycles is at most $r$, so the extra relative cost is at most $r a'e^{-k/15}\le(100k)^2 e^{-k/15}<1/2$ since $k\ge10^4$.

When $j\le p/4$, one has $a'\ge3a/4$ and hence $f(m,p-j,k)/\alpha_{n,p}<15/2$. The sum over $j$ of the binomial point masses in $\lambda_p$ is at most their maximum plus $p/(n+1)$ by unimodality and the beta integral. Stirling bounds the maximum by $1/\sqrt k$ using $k\ge10^4$, $n\ge20k$; also $p/(n+1)<7/(50\sqrt k)$. For $j>p/4$, the binomial mean exceeds $n/4\ge5k$, so the lower tail is at most $e^{-k}$. Its relative cost is at most $(100k)^2e^{-k}<1/1000$, using $\alpha_{n,p}^{-1}\le p$. The word boundary errors for the two rows cost less than $1/1000$ relatively after multiplication by $p$, by the bound on $4v^3e^{-4v/5}$. Thus all local indices satisfy

$$
\frac{p|\alpha_{n+1,p}-\alpha_{n,p}|}{\alpha_{n,p}}
<\frac{(15/2)(57/50)}{100}+\frac2{1000}<\frac1{10}.
$$

## Root isolation and the direct next-row comparison

The [earlier exterior theorem][front] gives ranks through $H_0=\lfloor7v/20\rfloor$. Take $H_0<h\le H$. Let $\rho=\alpha_{n,h}/\alpha_{n,h+1}$, $u=\rho(h/(h+1))^n$, and define

$$
F(z)=\frac{E_{n,k}(uz)}{\alpha_{n,h}h^n(uz)^h}.
$$

Its two central terms are $1,z$. The coefficient envelope gives $\rho\le17/5$ and $\rho^{-1}\le9/8$. The normalized base terms without the $\rho$ and $z$ factors have consecutive outward ratios at most $q=19/1000$. Indeed their first outward ratios are bounded by $\exp(-n/(h+1)^2)<q$ since $h+1\le(501/1000)v$.

At a local term $p=h-l$ the normalized coefficient ratio is at most $(10/3)(1+l/300)$; at $p=h+1+l$ it is at most $(9/8)^l$. Thus for modulus between $r_-$ and $r_+$ the two local geometric parameters are

$$
s=\frac{(19/1000)(9/8)}{r_-},
\qquad
b=(19/1000)(17/5)(9/8)r_+.
$$

The two absolute local tails together are bounded by

$$
\frac{10}{3}\left(\frac{s}{1-s}+\frac{s}{300(1-s)^2}\right)
+r_+\frac{b}{1-b}.
$$

For nonlocal indices, the distance from the central pair is at least $L=\lfloor v/25\rfloor\ge40$. On $1/2\le|z|\le3$ both outward parameters without the local coefficient factor are below $1/5$. Both central inverse coefficients are at most $v/18$. Hence the sum of the far tails is less than $(4v/18)\sum_{l\ge L}5^{-l}$. Even after multiplication by $2(n+1)$ this is less than $v^3 5^{-L}<1/1000$, checked at $L=40$ and using $v<25(L+1)$.

The exact comparison of local and far tails gives $|F-(1+z)|<1/4$ on $|z+1|=1/4$, less than $1/2$ on $|z|=1/2$, and less than 2 on $|z|=3$. Rouché on $z^{h-1}F(z)$ gives one zero in the first disk, $h-1$ inside the smaller circle and $h$ inside the larger circle. The first disk lies in the intervening annulus, so its unique zero is real by conjugation, simple, negative after rescaling and of rank $h$ in modulus.

At that root put $t=uz$. To evaluate the actual next row, subtract $h E_{n,k}(t)=0$ and divide by $\alpha_{n,h} h^n t^h$. The resulting scale has two parts. The old normalized terms acquire weight $p-h$, whose central contribution is $z$. A second part comes from $p(\alpha_{n+1,p}-\alpha_{n,p})$, relative to $\alpha_{n,p}$ where the index is local. The latter absolute local sum is bounded by $(1/10)(1+5/4+1/4)$. For the weighted old tails, the local bounds on the root disk give

$$
\frac{10}{3}\left(\frac{s}{(1-s)^2}
 +\frac{s(1+s)}{300(1-s)^3}\right)
+\frac54\left(\frac1{(1-b)^2}-1\right),
$$

with $r_-=3/4$, $r_+=5/4$. The two nonlocal contributions together cost less than $1/1000$ by the far bound, using $|p-h|\le n+1$ and $p|\alpha_{n+1,p}-\alpha_{n,p}|\le n+1$. The checked sum of these three errors is below $3/4\le|z|$. The scaled next row is therefore negative. Since $t^h$ has sign $(-1)^h$ and division by $t$ introduces one more negative sign, $P_{n+1}(t)$ has the desired sign $(-1)^h$.

## Join and effective consequence

The largest front modulus is less than $(17/4)(H/(H+1))^n$. At $\theta_*=(H+1)\pi/n$, use $\pi\cot\theta_*<n/(H+1)$ and

$$
n\log(1+1/H)-n/(H+1)\ge n/[2(H+1)^2]>3/2>\log(17/4).
$$

Thus the front lies strictly before the sample. Also $\theta_*>\pi/(2\sqrt n)$, so the sine Taylor bound on the right-hand angle gives $n\sin^2\theta_*>49/20$. At the stronger join, the established degree-split middle proof can use $49/20$ in place of $6/5$ in both pole envelopes and the join row cutoff. See [enhanced middle and uniform cutoff](middle.md).

Run `python3 -I -B check.py` for the [rational comparisons](front-output.txt). [Independent review](review.md) · [Independent checker](verify-independent.py)

**Formal verification** ⬜ None. The all-size conjecture remains open outside the known sufficient regions. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#permutations-with-long-cycles)

[front]: ../effective-front.md
