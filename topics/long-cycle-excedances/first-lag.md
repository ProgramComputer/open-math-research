# Interlacing when a second cycle first becomes possible

**Partial theorem.** Put $P_n(t)=E_{n,k}(t)/t$, where $E_{n,k}$ counts permutations of $[n]$ with every cycle of length at least $k$, by excedances. For every $k\ge3$, $P_{2k-1}$ and $P_{2k}$ have simple negative roots that strictly interlace, with $P_{2k}$ supplying both outer roots. At every root $x$ of $P_{2k-1}$, the new-cycle term in the insertion recurrence has magnitude strictly smaller than the derivative term. The proof uses exact integer signs for $3\le k\le200$ and estimates for $k\ge201$. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4) · [Independent agent-assisted review](review-first-lag.md)

## The two signs to check

Let $A_m(t)$ be the usual Eulerian polynomial, with degree $m-1$ for $m\ge1$, constant term one and reciprocal coefficients. A cycle of length $l$ has excedance enumerator $tA_{l-1}(t)$. For $k\le n<2k$, every allowed permutation is one cycle, so $P_n=A_{n-1}$. At $n=2k$, the other possibility consists of two $k$-cycles. Choosing the other labels of the cycle containing $2k$ gives the factor $B=\binom{2k-1}{k-1}$. Write
$$
 M=2k-2,\quad j=k-1,\quad P=A_M,\quad L=BtA_j^2,\quad Q_\pm=A_{M+1}\pm L .
$$
Then $P_{2k}=Q_+$. By the Eulerian recurrence $A_{M+1}=(1+Mt)A_M+t(1-t)A_M'$, the derivative term at a zero $x$ of $P$ is $A_{M+1}(x)$. The recurrence also gives simplicity and strict interlacing for the Eulerian rows, starting at $A_1=1$. At rank $h$ from zero the derivative term has sign $(-1)^h$, and the constant and leading terms of the new polynomial supply the two outer signs. Thus the same alternation holds for both $Q_\pm$ if
$$
 \mu(x)=\frac{L(x)}{A_{M+1}(x)},\qquad |\mu(x)|<1 .
 \tag{1}
$$
Both $Q_\pm$ are reciprocal of degree $M$ with extreme coefficients one. In particular $\mu(1/x)=\mu(x)$, so it suffices to check $x\in[-1,0)$.

## Exact finite range

For each $k$ from $3$ to $200$, the archive gives $k-2$ disjoint dyadic intervals in $(0,1)$ for the moduli of the roots of $P$ below one. Their endpoint signs for $P(-X)$ are $(-1)^{h-1},(-1)^h$, in ascending order $h=1,\ldots,k-2$. Their reciprocal partners and the root $-1$ exhaust the old degree. The checker evaluates $Q_+$ and $Q_-$ at both endpoints of every interval and verifies the common sign $(-1)^h$. It also verifies that both pencils have sign $(-1)^{k-1}$ at $-1$. Together with the sign $+1$ at zero these signs force $k-1$ pencil roots in the gaps on the side of moduli below one. Reciprocity yields $k-1$ other roots above one, exhausting the degree. Each pencil therefore has constant nonzero sign throughout each old bracket and the two signs agree at all old roots. This proves (1).

The checker rebuilds the Eulerian coefficients by their integer recurrence. At each interior dyadic point it uses integer Horner evaluation at a growing binary scale. Each rounding has magnitude less than one scaled unit and subsequent multiplication by the modulus, strictly below one, contracts it. The number of coefficients bounds the total rounding error. Floating-point estimates enter only when generating candidate brackets, which are checked again by the exact signs. [Archive](first-lag-prefix.jsonl.gz) · [Checker](verify_first_lag.py)

~~~sh
python3 -I -O topics/long-cycle-excedances/verify_first_lag.py
~~~

## Small ranks for $k\ge201$

Put $E=tA_M$ and write $[t^p]E=p^M\alpha_p$, with zero coefficients beyond its degree. Cutting a permutation at its descents gives $p$ increasing runs. Assigning each label its run number embeds these permutations in the $p^M$ words on $p$ colors. Every word in which each color occurs in each half of $[M]$ yields a permutation with $p$ runs by sorting the labels in each color and concatenating the runs in color order. Hence $0\le\alpha_p\le1$, and, for $p\le(17/40)\sqrt M$,
$$
 1-\alpha_p\le 2p\, e^{-M/(2p)}
 \le \tfrac{17}{20}\sqrt M\,e^{-20\sqrt M/17}<1/100
 \qquad(M\ge400).
 \tag{2}
$$
In the last bound the function decreases for $\sqrt M\ge20$.

Let $H=\lfloor3\sqrt M/8\rfloor$, $1\le h\le H$, and $u=(h/(h+1))^M$. Then $h+1\le(17/40)\sqrt M$. Define
$$
 F(z)=\frac{E(uz)}{h^M(uz)^h}=\sum_{p\ge1}\alpha_p b_p z^{p-h},
 \qquad
 b_p=\left(\frac ph\left(\frac h{h+1}\right)^{p-h}\right)^M .
$$
The terms $b_h,b_{h+1}$ are both one. Successive ratios away from these two terms, omitting the left side for $h=1$, are bounded by
$$
 (1-1/h^2)^M,\quad (1-1/(h+1)^2)^M
 \ \le\ q=e^{-5}<1/100 .
$$
Indeed the two displayed ratios occur at the first step and decrease further out. On $1/2\le |z|\le3$,
$$
 |F(z)-(1+z)|\le 4/100+\frac{2q}{1-2q}+\frac{9q}{1-3q}<1/2.
$$
On $|z+1|=1/8$, use $s_0=1/50$, which bounds $q|z|$ and $q/|z|$ there. The two tails are at most $(1+9/8)s_0/(1-s_0)$ and the leading coefficient errors at most $(1+9/8)/100$, giving a total less than $1/8$. Apply Rouché to $z^{h-1}F$ on each of the three circles. The origin-centered circles of radii $1/2$ and $3$ contain respectively $h-1$ and $h$ roots, and the disk about $-1$ contains one root. The latter is real by conjugation, simple, and of rank $h$ from zero. Write $x=uz$ for this root and $X=|x|$. In particular $7/8<X/u<9/8$.

At this root $xE'(x)/(h^M x^h)=zF'(z)$. In the differentiated sum the $p=h+1$ term has magnitude greater than $(99/100)(7/8)$. The remaining terms have absolute sum at most
$$
 \sum_{\ell\ge1}\ell s_0^\ell
 +2\sum_{\ell\ge1}(\ell+1)s_0^\ell
 =\frac{3s_0}{(1-s_0)^2}+\frac{2s_0}{1-s_0}<11/100.
$$
Thus $|xE'(x)|>(3/4)h^M X^h$.

The same injection into words gives the coefficient bound $[t^p](tA_j)\le p^j$. Use
$p(r-p)=r^2/4-(p-r/2)^2$ and $(1-y)^j\le e^{-jy}$ for $0\le y\le1$ to obtain
$$
 |x A_j(x)|^2
 \le \sum_{r\ge2} X^r\sum_{p=1}^{r-1}[p(r-p)]^j
 \le 4^{-j}\sum_{r\ge2}r^{M}X^r
       \left(1+\frac{\sqrt\pi\,r}{\sqrt j}\right).
 \tag{3}
$$
For the last estimate the Gaussian $\exp(-4j(p-r/2)^2/r^2)$ sums to at most $1+\sqrt\pi\,r/(2\sqrt j)$ over the integer lattice. To see the integral bound, count the number of lattice points in each positive superlevel set, bounded by its interval length plus one, then integrate the level between zero and one.

After division by $h^M X^h$, the weights $r^M X^r$ in (3) equal $b_r |z|^{r-h}$. The two middle terms are at most $1$ and $9/8$. The left tail is bounded termwise by $s_0^\ell$ at $r=h-\ell$, and the right by $(9/8)s_0^\ell$ at $r=h+1+\ell$. Since $j=M/2\ge200$ and $h+1\le(17/40)\sqrt M$, the factor in parentheses is below $21/10$ through $r=h+1$, and below $21/10+\ell/7$ at $r=h+1+\ell$. The normalized sum is therefore below
$$
 \frac{21}{10}\frac{1+9/8}{1-s_0}
 +\frac{9}{56}\frac{s_0}{(1-s_0)^2}<5.
$$
Finally $4^{-j}\binom{2j}{j}\le1/\sqrt{j+1}$, by induction using
$(2j+1)^2(j+2)\le4(j+1)^3$, so $4^{-j} B<2/\sqrt{k}$. Since $A_{M+1}(x)=(1-x)E'(x)$, this gives
$$
 |\mu(x)|=\frac{B\,|xA_j(x)|^2}{(1+X)|xE'(x)|}
 <\frac{40}{3\sqrt{k}}<1
 \qquad(k\ge201).
 \tag{4}
$$

## Pole estimates and the join

For $x=-e^{-s}$ with $s\ge0$, set $r=\sqrt{s^2+\pi^2}$, $\theta=\arg(s+i\pi)$, $C=\cos\theta$, $S=\sin\theta$, and $z_p=(C+ipS)^{-1}$ for odd integers $p$. Define $D_m=\sum_{p\ {\rm odd}} z_p^m$ for integers $m\ge2$. The Eulerian power-sum identity and the poles of $1/(1+e^{w-s})$ give
$$
 \frac{xA_m(x)}{m!(1-x)^{m+1}}= r^{-m-1}D_{m+1}\qquad(m\ge1).
 \tag{5}
$$
Indeed the left side equals the coefficient of $w^m$ of $1/(1+e^{w-s})-1$. This follows by first expanding $xe^w/(1-xe^w)$ for $|x|<1$ and then extending to $x=-1$ by continuity. Each pole $s+ip\pi$ has residue $-1$. On circles $|w|=\sqrt{s^2+4b^2\pi^2}$ with integer $b\to\infty$ the circle coefficient integral tends to zero because for fixed $s$ these circles have distance bounded below from the poles, so the inverse denominator is bounded on them. In detail, when $|\Re w-s|\ge1/4$, reverse triangle inequality gives a positive lower bound on $|1+e^{w-s}|$. Otherwise the distance from the nearest pole also bounds the distance of $\Im w$ from the nearest odd multiple of $\pi$ away from zero, and the same lower bound follows from the sine term in
$|1+e^{a+iy}|^2=(1-e^a)^2+4e^a\cos^2(y/2)$.
The coefficient equals the sum of $1/(s+ip\pi)^{m+1}$, giving (5).

Suppose $MS^2\ge1$, and put $v=M+1=2k-1$. For $p>0$,
$$
 |z_p|=(1+(p^2-1)S^2)^{-1/2},\qquad |z_p-C|\le p S .
$$
The second inequality follows by writing the quotient as
$S(S-ipC)/(C+ipS)$. For $v\ge100$ with $vS^2\ge1$, monotonicity of $(1+a/v)^v$ for $a\ge0$ gives
$$
 \sum_{p=3,5,\ldots}p|z_p|^v
 \le 3(27/25)^{-50}+\frac{25}{49}(27/25)^{-49}<1/10 .
 \tag{6}
$$
Here the tail after the first summand is at most half the integral from $3$ to infinity of the decreasing function $y(1+(y^2-1)/100)^{-50}$. At an old root $D_v=0$, so $|\cos(v\theta)|<1/10$ by (6) and $z_{\pm1}=e^{\mp i\theta}$. In $D_{v+1}-C D_v$ the principal pair contributes $-2S\sin(v\theta)$; the rest has magnitude below $2S/10$. It follows that
$$
 |D_{2k}|>2S(\sqrt{99/100}-1/10)>(7/4)S.
 \tag{7}
$$
For the numerator, $kS^2\ge k/M>1/2$ and $k\ge200$. The same monotonicity bounds $|z_p|^k$ by $(1+(p^2-1)/400)^{-100}$. Integral comparison and $y/3\ge1$ for $y\ge3$ then give
$$
 \sum_{p=3,5,\ldots}|z_p|^k
 \le (51/50)^{-100}+\frac{400}{1188}(51/50)^{-99}<1/4.
$$
In particular, $|D_k|<5/2$. Substituting (5) into the ratio cancels all the powers of $r$ and $1-x$. The ratio of the factorials, including $B$, is $1/k$. Therefore
$$
 |\mu(x)|=\frac{|D_k|^2}{k|D_{2k}|}
 < \frac{25}{7kS}\le\frac{25\sqrt M}{7k}<1.
 \tag{8}
$$

To cover all old roots, take $\theta_l=l\pi/(M+1)$ for $H+1\le l\le M/2$, and extend to $l=M/2+1,\ldots,M-H$ by $\theta_l=\pi-\theta_{M+1-l}$. Their corresponding real points are $-\exp(-\pi\cot\theta_l)$. For the first angle, $\theta_{H+1}>3\pi\sqrt M/(8(M+1))$, whose sine exceeds $1/\sqrt M$ for $M\ge400$. For example put $a=3\pi\sqrt M/(8(M+1))$; then $a<3/50$, and $\sqrt M(a-a^3/6)\ge (3\pi/8)(400/401)(1-(3/50)^2/6)>1$. Thus (6) applies at all these lower-half samples and gives $E$ there the principal sign $(-1)^l$. On the upper half $E(1/x)=x^{-(M+1)}E(x)$ supplies the reflected signs, again $(-1)^l$.

The $H$ small roots precede the first sample in order of increasing modulus. Combine $s=\pi\cot\theta_{H+1}<(M+1)/(H+1)$ at that sample with
$$
 M\log(1+1/H)-\frac{M+1}{H+1}
 \ \ge\ \frac{M}{2(H+1)^2}-\frac{1}{H+1}
 \ >\ \log(9/8)
$$
by $H+1\le(17/40)\sqrt M$ and the positive Taylor series of $-\log(1-1/(H+1))$. The $H$ reciprocal small roots follow the last sample. There are $M-2H-1$ sign changes between samples, completing the $M-1$ old roots together with the $2H$ outside them. The middle roots on the side $-1\le x<0$ satisfy $MS^2\ge1$ and therefore (8). The small roots satisfy (4). Reflection gives (1) everywhere. The Eulerian recurrence also covers every preceding single-cycle pair $k\le n\le2k-2$.

## A total variation bound of two fails

At $k=5$, take the old row $n=9$. Here $P=A_8$ and $L=126tA_4^2$. There is a root of $A_8$ in $[-3583/50000,-1433/20000]$, since the endpoint signs differ, and $A_9>11$ and $A_9+20L<-1$ throughout this interval. The checker verifies these three facts with rational interval Horner arithmetic. At that root $\mu<-1/20$, which also holds at its distinct reciprocal partner.

The residues of $L(t)/[(1-t)tP(t)]$ at the old roots are $\mu(x)$. There is no pole at zero, and the residue at one is $-L(1)/P(1)=-9/5$. The function is $O(t^{-2})$ at infinity. Thus the signed sum of the old-root residues is $9/5$, but two of them below $-1/20$ imply $\sum_x|\mu(x)|>2$. This is a counterexample to a bound on the total variation of these residues. The individual bounds (1) still hold in this pair.

**⬜ None.** The argument uses exact integer checks on the finite range and a written proof for the rest.
