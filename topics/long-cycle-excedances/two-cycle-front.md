# An effective front-root estimate in the two-cycle band

Let $2k\le n\le3k-2$ and $n\ge100$. Write $M=n-1$, $E=E_{n,k}$, $P=E/t$, and $H=\lfloor(7/20)\sqrt M\rfloor$. For every $1\le h\le H$, $P$ has a simple negative root $x$ of absolute rank $h$. At each such root the insertion ratio satisfies
$$
\left|\frac{L(x)}{(1-x)xP'(x)}\right|<\frac{777}{80\sqrt M}<1,\qquad
L(t)=\binom n{k-1}A_{k-1}(t)E_{n+1-k,k}(t).
$$
Thus for every $k\ge50$ the estimate controls these first $H$ roots in every row of the band. The proof also works at any rank $h$ such that $h+1\le(451/1000)\sqrt M$.

## Coefficients of the old row

Write $\alpha_p=[t^p]E/p^M$ for $p\ge1$, with zero coefficients beyond the degree. A permutation with $p-1$ descents determines a word with $p$ colors by assigning each label to its increasing run. Sorting the labels within each color reconstructs the permutation. This gives $[t^p](tA_m)\le p^m$ for every $m\ge1$. If all colors occur in both halves of the label set, then concatenating the increasing color classes gives a descent at every boundary, so
$$
[t^p](tA_M)\ \ge\ p^M \bigl(1-2p e^{-\lfloor M/2\rfloor/p}\bigr).
$$
Since $E$ includes the single-cycle contribution $tA_M$, one has $\alpha_p\ge99/100$ whenever $p\le(451/1000)\sqrt M$ and $M\ge99$. In this range $p<\sqrt M/2$ and the error is below $\sqrt M e^{-9\sqrt M/10}<1/100$.

There are at most two cycles. The two-cycle contribution is
$$
\frac12\sum_{\ell=k}^{n-k}\binom n\ell(tA_{\ell-1})(tA_{n-\ell-1}).
$$
The word upper bound on its coefficient of $t^p$, after division by $p^M$, gives
$$
 \alpha_p\le 1+\frac12\sum_{s=1}^{p-1}\frac{p}{s(p-s)}
       \Pr\{\mathrm{Bin}(n,s/p)\in[k,n-k]\}
 =1+\sum_{s=1}^{p-1}\frac{1}{s}
       \Pr\{\mathrm{Bin}(n,s/p)\in[k,n-k]\}.
$$
The equality uses symmetry in $s,p-s$. For $s/p\notin(1/5,4/5)$, the binomial probability is at most $e^{-8n/225}$ by Hoeffding, since $k\ge n/3$. For $p\le n-1$ the contribution of these $s$ is at most $(1+\log n)e^{-8n/225}<1/6$. The expression decreases for $n\ge100$, and at $n=100$ the inequality follows from $\log100<14/3$ and $e^{32/9}>34$. For $p\le4$, the sum of $1/s$ over the remaining $s$ is at most $1+1/2+1/3=11/6$. For $5\le p\le11$ all the remaining $s$ belong to $[2,8]$, whose harmonic sum is below $11/6$. For $p\ge12$, if the remaining indices run from $a$ to $b$, their sum is at most
$$
1/a+\log(b/a)\le 5/p+\log 4<11/6.
$$
Consequently $0\le\alpha_p\le3$ for every $p$, including the zero coefficients.

## Root isolation and a lower bound on the derivative

For a rank under consideration let
$$
\rho=\frac{\alpha_h}{\alpha_{h+1}},\qquad
u=\rho\left(\frac{h}{h+1}\right)^M,\qquad
F(z)=\frac{E(uz)}{\alpha_h h^M(uz)^h},\qquad
b_p=\left(\frac{p}{h}\left(\frac{h}{h+1}\right)^{p-h}\right)^M.
$$
Then $\rho,\rho^{-1}\le R=100/33$. The $p=h,h+1$ terms of $F$ are exactly $1,z$. The weights $b_h,b_{h+1}$ equal one. Away from these two indices the ratios of successive $b_p$ are bounded by $(1-1/h^2)^M$ on the left and $(1-1/(h+1)^2)^M$ on the right, with an empty left side when $h=1$. Since $h+1\le(451/1000)\sqrt M$, both ratios are below
$$
q=\exp(-1000000/203401)<1/135 .
$$
For $1\le h\le H$ the hypothesis on $h+1$ follows from $7/20+1/\sqrt{99}<451/1000$.

Write $T_p$ for the term of $F$ indexed by $p$. At any $z\ne0$ for which $q\max(|\rho z|,|\rho z|^{-1})\le s$,
$$
 |T_{h-\ell}|\le Rs^\ell,\qquad
 |T_{h+1+\ell}|\le R|z|s^\ell\qquad(\ell\ge1).
$$
On the right this uses the coefficient ratio $\alpha_{h+1+\ell}/\alpha_{h+1}$ because the central right term is exactly $z$. On $|z+1|=1/4$ one may take $s=3/100$, since $3/4\le |z|\le5/4$ and $(4/3)Rq<3/100$. Therefore
$$
|F(z)-(1+z)|\le R(1+|z|)\frac{s}{1-s}<1/4.
$$
On the two circles $|z|=1/2$ and $|z|=3$ one may instead use $s=7/100$. The same bound is strictly below $1/2$ and $2$, respectively. Rouché applied to the polynomial $z^{h-1}F(z)$ gives $h-1$ roots inside $|z|=1/2$, $h$ inside $|z|=3$, and one inside the disk about $-1$. The disk lies within the annulus between the two origin-centered circles, so it contains the only root in that annulus. This root is real by conjugation. Thus $x=uz$ is the simple negative root of absolute rank $h$, with $3/4<X/u<5/4$ for $X=|x|$.

At this root, $xE'(x)=\alpha_h h^M x^h zF'(z)$. Use $F(z)=0$ to write $zF'(z)=zF'(z)-F(z)$. Its central contribution is $-1$. The two tails now have weights $\ell+1$ on the left and $\ell$ on the right. With $s=3/100$, their combined magnitude is at most
$$
R\left((1+5/4)\frac{s}{(1-s)^2}+\frac{s}{1-s}\right)<1/3.
$$
In particular,
$$
|xE'(x)|>\frac23\alpha_h h^M X^h .
$$

## A uniform bound on the new-cycle contribution

Since $k\le n+1-k<2k$, the factor $E_{n+1-k,k}$ is the single-cycle row $tA_{n-k}$. Thus the coefficient bound from words gives
$$
[t^r](tL)
 \le \binom n{k-1}\sum_{s=1}^{r-1}s^{k-1}(r-s)^{n-k}
 =\frac{n}{n-k+1}r^M
 \sum_{s=1}^{r-1}\Pr\{\mathrm{Bin}(M,s/r)=k-1\}.
$$
Here $a=(k-1)/M$ lies in $[1/3,1/2]$ and $n/(n-k+1)<2$. The binomial probability at $a$ is bounded by
$$
\Pr\{\mathrm{Bin}(M,a)=k-1\}
 \le \frac{e^{1/(12M)}}{\sqrt{2\pi M a(1-a)}}<\frac{7}{8\sqrt M}
$$
by Stirling and $a(1-a)\ge2/9$. At an arbitrary parameter $b$, its ratio to the probability at $a$ is $\exp(-M D(a\|b))$, where $D(a\|b)=a\log(a/b)+(1-a)\log((1-a)/(1-b))$. As a function of $a$ its second derivative is at least four, and its value and first derivative vanish at $a=b$. Hence $D(a\|b)\ge2(a-b)^2$. Summing the corresponding Gaussian over the grid $s/r$ gives
$$
[t^r](tL)\le \frac{2(7/8)}{\sqrt M}\,r^M
     \left(1+\sqrt{\frac\pi2}\frac{r}{\sqrt M}\right).
$$
For the Gaussian bound, count lattice points in each superlevel interval by its length plus one, then integrate the level from zero to one.

For the sum at $x$, divide the weights $r^M X^r$ by $\alpha_h h^M X^h$. At $r=h-\ell$ they are at most $(100/99)s^\ell$ for $\ell\ge0$ and at $r=h+1+\ell$ they are at most $(100/99)(5/4)s^\ell$ for $\ell\ge0$, again with $s=3/100$. These bounds use $1/\alpha_h$ on the left and $1/\alpha_{h+1}$ on the right. Since $h+1\le(451/1000)\sqrt M$, the parenthetical weight is at most $157/100$ through $r=h+1$. It grows by less than $13/100$ at each step afterwards. Hence the normalized weighted sum is at most
$$
\frac{100}{99}\left(\frac94\frac{157}{100(1-s)}
       +\frac54\frac{13s}{100(1-s)^2}\right)<\frac{37}{10}.
$$
Here $\sum_{\ell\ge0}\ell s^\ell=s/(1-s)^2$. Since $xP'(x)=E'(x)$ at a root, the displayed coefficient bound and derivative lower bound give
$$
\left|\frac{L(x)}{(1-x)xP'(x)}\right|
 =\frac{|xL(x)|}{(1+X)|xE'(x)|}
 <\frac{2(7/8)(37/10)}{(2/3)\sqrt M}
 =\frac{777}{80\sqrt M}<1 .
$$

## Location relative to the usual first pole sample

If the first bulk checkpoint is taken at $\theta_{H+1}=(H+1)\pi/(M+1)$ and $x_{\rm check}=-\exp(-\pi\cot\theta_{H+1})$, all $H$ front roots precede it in increasing modulus. Indeed $X_h<(5/4)R(H/(H+1))^M$ and $\pi\cot\theta_{H+1}<(M+1)/(H+1)$, while
$$
M\log(1+1/H)-\frac{M+1}{H+1}
 \ge \frac{M}{2(H+1)^2}-\frac1{H+1}
 \ge\frac{1}{2(451/1000)^2}-\frac14
 >\log((5/4)R).
$$
The checkpoint also satisfies $M\sin^2\theta_{H+1}>1$. In fact $\theta_{H+1}>(7\pi/20)\sqrt M/(M+1)$, and the sine of this lower bound exceeds $1/\sqrt M$ by $\sin b\ge b-b^3/6$, $b<112/1000$, and $M/(M+1)\ge99/100$. For the bulk bound $n\sin^2\theta\ge6/5$, the same sample suffices whenever $n=M+1\ge192$. Put $b=(7\pi/20)\sqrt{n-1}/n$. Then $b^2<121/(100n)$ by $\pi<22/7$, so the sine lower bound gives
$$
 n\sin^2\theta_{H+1} >
 \frac{49}{400}\left(\frac{314159}{100000}\right)^2
 \frac{191}{192}\left(1-\frac{121}{115200}\right)^2>\frac65 .
$$
The last inequality is a comparison of rationals. The signs at these checkpoints and the middle-root estimates use the separate bulk argument.
