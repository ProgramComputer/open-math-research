# Effective front roots for all minimum cycle lengths

**Partial theorem.** Let $n\ge10{,}000$ and $3\le k\le n$. Set $H=\lfloor7\sqrt n/20\rfloor$ and $P_n=E_{n,k}/t$. For every $1\le h\le H$, the root of $P_n$ of absolute rank $h$ is simple and negative. At each such root $x$, the distinguished-cycle term $L=\binom n{k-1}A_{k-1}E_{n+1-k,k}$ in the insertion recurrence satisfies
$$
|L(x)|<|x(1-x)P_n'(x)|.
$$
In order of increasing absolute value, the new rank-$h$ root is strictly closer to zero than the old rank-$h$ root. All higher-rank new roots are farther from zero than that old root. All $H$ old roots precede the phase sample $t=-\exp(-\pi\cot((H+1)\pi/n))$. The reciprocal conclusions hold at the other end. There is no restriction on the number of cycles. The proof compares the run-color probabilities for consecutive rows and bounds the remaining terms on three circles.

Use the [run encoding and insertion recurrence](proof.md). For each $p\ge1$ write $\alpha_{N,p}=[t^p]E_{N,k}/p^N$, which is the probability that an independent uniform word of length $N$ on $p$ run colors and a uniform permutation of the colors satisfy all upward boundaries and minimum lengths. Write $f(N,p,k)$ for the acceptance probability for the minimum lengths alone. It bounds $\alpha_{N,p}$ above. Put $f(N,p,k)=0$ for $0<N<k$ when $p\ge1$. The good event that every color appears in both label halves guarantees the upward boundaries and all nonempty colors, so
$$
0\le f(N,p,k)-\alpha_{N,p}\le 2p e^{-\lfloor N/2\rfloor/p}.
\tag{1}
$$
This argument uses the probability form of the coefficients from the [uniform proof](uniform-interlacing.md) and the adaptive root scaling from the [two-cycle front estimate](two-cycle-front.md).

## Effective run-color acceptance envelopes

Put $J=\lfloor\sqrt n/2\rfloor$. For $p\le J$ and $a=kp/n$, the old row satisfies
$$
\frac{99}{100(1+(8/3)a)}\le\alpha_{n,p}\le
\min\left(1,\frac{151}{100a}\right).
\tag{2}
$$
The upper bound also applies to $f(N,p,k)$ with $a$ replaced by $kp/N$ for every $n/2\le N\le n$ and $1\le p\le J$.

For the lower bound when $k\le n/2$, let $b=\lceil (4/3)a\rceil$, so $b\le p$. Write $d(p,b)$ for the probability that a uniform permutation of $p$ colors has no cycle shorter than $b$. Distinguishing the cycle containing a fixed color gives $1/(2b-1)\le d(p,b)\le1/b$ for $p\ge b$. Condition the run permutation to have no cycle shorter than $b$. A cycle of $u\ge b$ colors receives a binomial number of labels of mean $nu/p\ge4k/3$, so its probability of receiving fewer than $k$ labels is at most $e^{-nu/(32p)}$. For $u<p$, the unconditional expected count of marked $u$-cycles whose remaining cycles also have length at least $b$ is $d(p-u,b)/u\le1/(bu)$. A cycle of length $p$ receives every label and cannot fail. After division by $d(p,b)$, the union bound over the marked cycles is therefore less than
$$
2\sum_{u\ge1} \frac{e^{-nu/(32p)}}{u}
\le \frac{2e^{-25/4}}{1-e^{-25/4}}<\frac1{250}.
$$
The error in (1) relative to $d(p,b)$ is bounded by $4p^2 e^{-(n-1)/(2p)}\le n e^{-(n-1)/\sqrt n}<1/1000$. Thus $\alpha_{n,p}\ge(99/100)d(p,b)\ge99/[100(1+(8/3)a)]$. When $k>n/2$, acceptance for the size condition requires a single run cycle and has probability $1/p$. Applying (1) gives the same lower bound.

For the upper bound take $\mu=N/p\ge\sqrt n$, $a'=k/\mu$ and $b=\max(1,\lceil (2/3)a'\rceil)$. The bound is immediate if $k>N$ or $a'\le3/2$. Otherwise, acceptance with a run cycle of $u<b$ colors requires that this cycle receive at least $k$ labels despite mean $Nu/p<(2/3)k$. The exponential binomial tail is at most
$$
\exp[-k(\log(3/2)-1/3)]\le e^{-k/15}.
$$
Using the unconditional expected number $1/u$ of $u$-cycles gives
$$
f(N,p,k)\le d(p,b)+(1+\log p)e^{-k/15}
\le\frac{3}{2a'}+(1+\log p)e^{-a'\mu/15}.
$$
The last error times $a'$ is at most $(3/2)(1+\log(\sqrt n/2))e^{-\sqrt n/10}<1/100$. This uses decrease in $a'$ for $a'\ge3/2$, decrease in $\sqrt n$ for $\sqrt n\ge100$, and the bounds $p\le\sqrt n/2$ and $\mu\ge\sqrt n$. This proves (2).

## Lag coefficients and consecutive row stability

Write $m=n+1-k$. If $m<k$ the lag vanishes and we set $\lambda_p=0$. Otherwise $n/2\le m\le n$, and for $p\ge1$ we put
$$
\lambda_p=\sum_{j=1}^{p-1} b(j/p)f(m,p-j,k),
\qquad
b(y)=\binom n{k-1}y^{k-1}(1-y)^m.
$$
Then
$$
[t^p](tL)\le p^n\lambda_p,\qquad
0\le f(n+1,p,k)-f(n,p,k)\le \lambda_p/p .
\tag{3}
$$
For the first bound, the coefficient of $t^j$ in $tA_{k-1}$ is at most $j^{k-1}$ by assigning the $k-1$ labels of a permutation to its increasing runs. Convolve with $[t^{p-j}]E_{m,k}=(p-j)^m\alpha_{m,p-j}$. Division by $p^n$ uses $k-1+m=n$, giving the one binomial point mass in (3). For the second bound, couple the word of length $n+1$ to the old word by appending an independent color. If the minimum-size condition changes from false to true, the new label hits a run cycle that had precisely $k-1$ labels. A cycle of $j$ colors contributes expected count $1/j$ and is hit with probability $j/p$. Conditional on the count $k-1$, the remaining labels use the other $p-j$ colors independently and uniformly, and the remaining run permutation is uniform. The all-color cycle cannot have had size $k-1$. The same argument makes both differences zero when $m<k$, and both vanish for $p=1$. For use outside the range of (2), $\lambda_p\le p$ follows directly.

For $p\le J$ the useful uniform estimate is
$$
\lambda_p\le \frac8{25}\alpha_{n,p}.
\tag{4}
$$
If $k\le3n/(4p)$, set $\mu=n/p$. The sample $b(j/p)$ is bounded by $\Pr\{\mathrm{Bin}(n,j/p)\le k-1\}\le e^{-j\mu/32}$ for every $j\ge1$. Hence $\lambda_p<1/500$, while $\alpha_{n,p}\ge33/100$ by (2).

Otherwise $k-1\ge150$. Put $y_0=(k-1)/n$. A sample with $j/p\le y_0+1/10$ has residual parameter
$$
\frac{k(p-j)}m\ge\frac45\frac{kp}n
$$
because $m/n=1-y_0\ge1/2$. The upper bound from (2) for the residual and the lower bound for $\alpha_{n,p}$ give
$$
\frac{f(m,p-j,k)}{\alpha_{n,p}}
\le \frac{100}{99}(1+(8/3)a)\min\left(1,\frac{151}{80a}\right)
<\frac{61}{10}.
$$
For $j/p>y_0+1/10$, the ratio of $b(j/p)$ to its maximum at $y_0$ is $\exp(-nD(y_0\|j/p))$. Here $D$ is Bernoulli relative entropy and $D(v\|w)\ge2(v-w)^2$, by the second derivative in $v$. Hence $b(j/p)\le e^{-n/50}$. Summing these samples after division by $\alpha_{n,p}$ costs at most $n e^{-n/50}<1/10{,}000$, using $p(1+(8/3)a)/(99/100)<n$.

Stirling's bounds give $b(y_0)\le e^{1/(12n)}/\sqrt{2\pi(k-1)(1-y_0)}<47/1000$. The lattice sum of the unimodal kernel is at most its integral times $p$, plus its maximum. This follows by omitting the largest sample and charging each other sample to the adjacent interval toward the largest one. The beta integral is $1/(n+1)$. Since $p/(n+1)<1/200$, the total relative cost is at most
$$
\frac{61}{10}\left(\frac{47}{1000}+\frac1{200}\right)+\frac1{10{,}000}
<\frac8{25}.
$$
This proves (4).

Equations (1), (3) and (4) also give
$$
\frac{|\alpha_{n+1,p}-\alpha_{n,p}|}{\alpha_{n,p}}\le \frac{33}{100p}
\quad(1\le p\le J).
\tag{5}
$$
Indeed the two boundary-error terms in (1), multiplied by $p/\alpha_{n,p}$, cost at most $2 n^{3/2}e^{-(n-1)/\sqrt n}<1/100$ by (2). The same upper bound for the two row sizes follows by using $\lfloor n/2\rfloor$ in both boundary terms. For $p=1$ the ratio between the two coefficients $\alpha$ is exactly one.

## Isolation at the adaptive radius

Fix $1\le h\le H$. Put $\rho=\alpha_{n,h}/\alpha_{n,h+1}$, $u=\rho(h/(h+1))^n$ and
$$
F(z)=\frac{E_{n,k}(uz)}{\alpha_{n,h}h^n(uz)^h},
\qquad
b_p^*=\left(\frac ph\left(\frac h{h+1}\right)^{p-h}\right)^n.
$$
The terms at $p=h,h+1$ are exactly $1,z$. On either side of these terms the ratios of consecutive $b_p^*$ away from the central pair are at most $q=e^{-n/(h+1)^2}$. This follows by evaluating the largest ratios at the two immediate neighbors, where the exact bases are $1-1/h^2$ and $1-1/(h+1)^2$. The left tail is empty for $h=1$.

From (2), for $p,v\le J$,
$$
\frac{\alpha_{n,p}}{\alpha_{n,v}}
\le \frac{51}{10}\max(1,v/p).
$$
Thus both $\rho$ and $\rho^{-1}$ are below 6 if $h\ge6$, and below $51/5$ for $h\le5$. In the first case $h+1\le(9/25)\sqrt n$, so $q<1/2200$. In the second case $q\le e^{-10000/36}$, which is more than enough for $q\max(\rho,\rho^{-1})<6/2200$ again. At $p=h-\ell$ the coefficient ratio to $\alpha_{n,h}$ is at most $(51/10)(\ell+1)$. At $p=h+1+\ell\le J$ the ratio to $\alpha_{n,h+1}$ is at most $51/10$. When $p=h+1+\ell>J$, we have $\ell>(7/50)\sqrt n$ and $h+1<(18/7)\ell$. Hence
$$
1/\alpha_{n,h+1}\le\frac{100}{99}(1+(8/3)(h+1))<8(\ell+1).
$$
These bounds, and $\alpha_{n,p}\le1$, give right-tail ratio at most $8(\ell+1)$ for every $p=h+1+\ell$.

Let $s$ be any upper bound on $q\max(|\rho z|,|\rho z|^{-1})$. At left index $h-\ell$ the absolute term is at most $(51/10)(\ell+1)s^\ell$, and at right index $h+1+\ell$ it is at most $8|z|(\ell+1)s^\ell$. Thus one can use $s=1/300$ on $|z+1|=1/8$, $s=3/500$ on $|z|=1/2$ and $s=9/1000$ on $|z|=3$. On these circles respectively the error in $F-(1+z)$ is less than $1/10$, $1/2$ and 2. These follow by multiplying $(51/10)+8|z|$ by $\sum_{\ell\ge1}(\ell+1)s^\ell=(1-s)^{-2}-1$. Rouché's theorem for $z^{h-1}F(z)$ gives respectively one root in the disk about $-1$, $h-1$ roots inside the half-radius circle and $h$ inside the radius-three circle. The disk sits in the resulting annulus. Its unique root is simple and negative by conjugation, and has absolute rank $h$.

At this root write $x=uz$, $X=|x|$. We have $|z+1|<1/8$. Since $F(z)=0$, the identity $xE_{n,k}'(x)/(\alpha_{n,h}h^n x^h)=zF'(z)-F(z)$ gives the two central terms $-1,0$. The remaining terms are bounded by
$$
\frac{51}{10}\left(\frac{1+s}{(1-s)^3}-1\right)
  +9\frac{2s}{(1-s)^3}<\frac3{20}\qquad(s=1/300).
$$
The two weights are $(\ell+1)^2$ on the left and $\ell(\ell+1)$ on the right, including the earlier coefficient-ratio factors. Thus $|xE'_{n,k}(x)|>(17/20)\alpha_{n,h}h^nX^h$.

## Signs and the join

In the scale $\alpha_{n,h}h^n X^h$, (3) and (4) bound the contribution of indices $p\le J$ to $|xL(x)|$ by at most $(8/25)$ times the absolute sum of the terms of $F(z)$, which is less than $(8/25)(1+9/8+1/10)$. For $p>J$ use $\lambda_p\le p$, $\ell=p-h-1\ge14$, $p<4\ell$, and the bound $1/\alpha_{n,h+1}<8(\ell+1)$. Their normalized sum is less than $36\sum_{\ell\ge14}\ell(\ell+1)(1/300)^\ell<1/1000$. Therefore $|xL(x)|<(18/25)\alpha_{n,h}h^nX^h<|xE'_{n,k}(x)|$. At an old root $xP_n'(x)=E'_{n,k}(x)$, so $|L(x)|<|x(1-x)P_n'(x)|$. The latter term has sign $(-1)^h$ because all $h-1$ smaller roots are negative and simple, and $P_n(0)=1$. Both signed insertions preserve this sign.

For consecutive order, let $u_{n,h}$ and $u_{n+1,h}$ be the two adaptive radii. At $p=h,h+1$, (5) bounds $\alpha_{n+1,p}/\alpha_{n,p}$ between $83/100$ and $117/100$ for $p\ge2$. At $p=1$ it equals one. The old root is therefore in the new rank-$h$ annulus $(u_{n+1,h}/2,3u_{n+1,h})$ in modulus. For $h\ge2$, its modulus divided by $u_{n+1,h}$ is between $(7/8)(83/117)$ and $(9/8)(117/83)(3/2)$. At $h=1$, it is between $(7/8)(83/100)2$ and $(9/8)(117/100)2$. The new polynomial has exactly one root in that annulus and sign $(-1)^{h-1}$ before that root. Its sign $(-1)^h$ at the old root places the old root strictly after it in modulus, with every other larger new root outside the annulus.

Finally every old front root has $X<(9/8)(51/5)(H/(H+1))^n$. At the next integer phase sample $\theta=(H+1)\pi/n$, one has $\pi\cot\theta<n/(H+1)$ and
$$
n\log(1+1/H)-\frac n{H+1}
\ge\frac n{2(H+1)^2}
\ge\frac1{2(9/25)^2}
>\log((9/8)(51/5)).
$$
Hence each of the $H$ front roots comes before this sample. The sample satisfies $n\sin^2\theta>6/5$ by $H+1>7\sqrt n/20$, $\sin y\ge y-y^3/6$ and $n\ge10{,}000$. Reflection gives the corresponding order and insertion signs at large modulus. The estimate leaves the middle-root argument as the remaining analytic step for this cutoff.

[Independent agent-assisted review](review-effective-front.md) · [Exact scalar checks](verify_front_constants.py)
