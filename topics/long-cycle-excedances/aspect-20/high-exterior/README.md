# Uniform exterior signs at heights 1,001–9,999 and aspect at least 20

Let $E_{n,k}(t)$ enumerate permutations by excedances when every cycle length is at least $k$, and put $P_n=E_{n,k}/t$ at fixed $k$. For $1001\le n<10{,}000$, $k\ge3$, and $n/k\ge20$, let $H=\lfloor7\sqrt n/20\rfloor$. The first $H$ old nonzero roots in modulus are simple and negative, and the actual next-row sign at old rank $h$ is $(-1)^h$ for $P_{n+1}$. The new root of rank $h$ lies before the old one in modulus and all higher new ranks lie after it. The entire old front lies strictly before the common-circle sample at angle $(H+5/6)\pi/n$ and the first integer-phase middle sample $(H+1)\pi/n$. Reciprocation gives the other end. This supplies the exterior input to a separately certified middle argument.

## Run colors and a uniform coefficient floor

Write $\alpha_{N,p}=[t^p]E_{N,k}/p^N$, the run-color acceptance probability. With $p$ colors, assign the labels independently and uniformly and take an independent uniform permutation of the colors. Each color cycle collects all labels assigned to its colors. The acceptance probability $f(N,p,k)$ tests minimum cycle lengths alone. The further run boundary and nonempty-color conditions give

$$
0\le f(N,p,k)-\alpha_{N,p}\le2p\exp[-\lfloor N/2\rfloor/p].
$$

Indeed every color appearing in both halves of the labels suffices for all these conditions, and the complementary event is bounded by a union bound. These are the same encoding and coupling as in the [effective exterior proof](../../effective-front.md).

For $1001\le N\le10{,}000$, $N/k\ge20$ and $p\le\lfloor7\sqrt N/20\rfloor+1$, we claim $\alpha_{N,p}>.30$. The case $p=1$ has $\alpha_{N,1}=1$. For $p\ge2$, condition the color permutation to have no fixed color. Its probability $d(p,2)$ belongs to $[1/3,1/2]$ by the elementary cycle-probability bounds. A full color cycle cannot fail. For $2\le j<p$, the conditional expected number of $j$-cycles is at most $3/(2j)$: it is $d(p-j,2)/(j d(p,2))$ and vanishes if the residual size is one. A $j$-cycle has mean $jN/p$ assigned labels. For $v=\sqrt N$, use $p\le .35v+1\le .382v$ and $v\le100$ to bound the binomial lower-tail exponent by

$$
\frac{jN}{2p}\left(1-\frac{p}{20j}\right)^2
\ge\frac{jv}{2(.382)}(.975-.00875v)^2>1.3j.
$$

The last function of $v$, without $j$, has its minimum at an endpoint of $[31.25,100]$ because the derivative changes from positive to negative. The conditional union bound is at most $(3/4)e^{-2.6}/(1-e^{-1.3})<.08$. Subtracting the word-boundary error gives $\alpha_{N,p}>.30$, since $1/3$ times the success probability exceeds $.30$ even after subtracting $.001$. All probability estimates here apply to both the old and new central coefficients.

## Appending one label

For $p\le\sqrt n/2$ we have the uniform absolute estimate

$$
p|\alpha_{n+1,p}-\alpha_{n,p}|<.1 .
$$

To see this, append a uniform color to the old word with the color permutation unchanged. Acceptance can only increase for the minimum-size event, and a newly accepted word must hit an old color cycle with exactly $k-1$ assigned labels. Summing over possible marked cycles gives

$$
0\le p(f(n+1,p,k)-f(n,p,k))
\le\sum_{j=1}^{p-1}b(j/p),\qquad
b(y)=\binom n{k-1}y^{k-1}(1-y)^{n+1-k}.
$$

Here the old mean count $1/j$ of $j$-cycles cancels their hit probability $j/p$ after multiplication by $p$. In the case $k\le n/(2p)$ a geometric lower-tail bound gives $\sum_{j\ge1}e^{-jn/(8p)}$, using $n/p\ge2\sqrt n$. Otherwise $k-1\ge31$ and the maximum of the unimodal kernel is bounded by

$$
\max b\le
\frac{e^{1/(12n)}}{\sqrt{2\pi(k-1)(1-(k-1)/n)}}<.075 .
$$

This is the ordinary Stirling bound at the continuous mode, with $1-(k-1)/n\ge19/20$. The sum of the kernel values on the $1/p$ lattice is at most its maximum plus $p$ times its integral, which is $p/(n+1)<.016$ by the beta integral. In passing from $f$ to $\alpha$, the two word-boundary errors after multiplication by $p$ cost at most $n\exp[-(n-1)/\sqrt n]<.001$ uniformly. This proves the estimate, and $p=1$ in fact has zero difference.

## Root brackets and actual next signs

For $1\le h\le H$, set $\rho=\alpha_{n,h}/\alpha_{n,h+1}$, $u=\rho(h/(h+1))^n$, and

$$
F(z)=\frac{E_{n,k}(uz)}{\alpha_{n,h}h^n(uz)^h}.
$$

The central terms are $1,z$, and $\max(\rho,\rho^{-1})<10/3$. The outward geometric ratios for the pure monomial bases are at most $q=e^{-n/(h+1)^2}<1/900$: the first ratios have exact bases $1-1/h^2$ and $1-1/(h+1)^2$, and the successive outward ones decrease. All coefficients satisfy $0\le\alpha_{n,p}\le1$, so ratios to the respective central coefficient are at most $10/3$. At modulus between $r_-$ and $r_+$ put $s_0=q(10/3)\max(r_+,1/r_-)$. Then the absolute tail bound is $(10/3)(1+r_+)s_0/(1-s_0)$. It is below $.05$ on $|z+1|=.05$, below $1/2$ at $|z|=1/2$, and below 2 at $|z|=3$. Rouché's theorem on $z^{h-1}F(z)$ gives one root in the disk about $-1$, and $h-1$ and $h$ roots within the two concentric circles. Consequently the root in the annulus is negative, simple and of rank $h$. The same analysis applies to the next row with its own adjacent balance $u_{n+1}$, since its central coefficient floor holds through size $10{,}000$.

At the real old root $t=uz$, divide $E_{n+1,k}(t)-hE_{n,k}(t)$ by $\alpha_{n,h}h^n t^h$. The old normalized terms acquire weight $p-h$ and give the central contribution $z<-.95$. The remaining terms from the size change have coefficients $p(\alpha_{n+1,p}-\alpha_{n,p})$ on the same pure monomial scales. For the two central terms their absolute sum is at most $(1+1.05)/3$. On the root disk we may take the geometric ratio $s=1/250$. The weighted old tails cost at most

$$
\frac{10}{3}\left(\frac{s}{(1-s)^2}
+1.05\big((1-s)^{-2}-1\big)\right)<.05.
$$

The noncentral changes with $p\le\sqrt n/2$ contribute below $(1+1.05)s/(3(1-s))<.003$. All other indices have $p=h+1+l$ with $l\ge4$ and $p<5l$, since $h+1\le.35\sqrt n+1\le.382\sqrt n$. Use $|\alpha_{n+1,p}-\alpha_{n,p}|\le1$ and sum $(10/3)(1.05)\sum_{l\ge4}5l s^l<.001$. Together these errors are below $.95$, so the scaled next row is negative and $P_{n+1}(t)$ has sign $(-1)^h$. This step works directly with the actual consecutive rows.

For order, the old coefficient ratio $\alpha_{n+1,p}/\alpha_{n,p}$ is in $[5/6,7/6]$ at central $p\ge2$, and equals one for $p=1$. Consequently $|t|/u_{n+1}\in(1/2,3)$, multiplying the old factor $|z|\in(.95,1.05)$ by the adjacent ratios and by $(h+1)/h$. At $t=-u_{n+1}/2$ the same Rouché tail bound gives sign $(-1)^{h-1}$ for $P_{n+1}$. Its unique annulus root is therefore closer to zero than the old root. All its remaining higher ranks are outside the larger annulus radius.

## Phase join

The last old exterior root has modulus below $(7/2)(H/(H+1))^n$. At $\theta_{\ast}=(H+5/6)\pi/n$ one has $\pi\cot\theta_{\ast}<n/(H+5/6)$. The integral of $1/(H+x)$ over $[0,1]$ is at least its value at the midpoint by convexity, so

$$
n\left(\log(1+1/H)-\frac1{H+5/6}\right)
\mathrel{>}\frac{n}{3(H+1)^2}\ge\frac1{3(.382)^2}>\log(7/2).
$$

This places the entire old front before the common-circle entrance. The integer sample $(H+1)\pi/n$ is later. The sine bound gives $n\sin^2\theta_{\ast}>1$ and $n\sin^2((H+1)\pi/n)>6/5$, using $.34\sqrt n<H+5/6$, $.35\sqrt n<H+1$, and both angles below $.039$. The common-circle entrance also has $\pi\cot\theta_{\ast}>2\sqrt n$ by the cosine bound. Reflecting across $t=-1$ gives the exterior signs and rank order on the other half-axis.

Run `python3 -I -B check.py` here for the rational scalar checks. No polynomial roots are tested by this checker. The proof controls continuous root brackets via the displayed inequalities, and has no Lean or Rocq verification. [Exact output](output.txt) · [Independent review and replay](review.md)
