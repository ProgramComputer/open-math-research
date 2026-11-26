# Eventual strict interlacing for all cycle-length thresholds

**Proposed theorem.** There is an absolute $N$ such that whenever $n\ge N$ and $3\le k\le n$, the $n-2$ nonzero roots of $E_{n,k}$ are simple and negative and they strictly interlace the nonzero roots of $E_{n+1,k}$. Zero is simple. The same $N$ applies to all thresholds. The proof leaves the finite set of smaller row sizes unresolved; it gives no numerical upper bound suitable for enumerating that set.

Use $a_{n,p}=[t^p]E_{n,k}(t)$, $\alpha_{n,p}=a_{n,p}/p^n$, and $P_n(t)=E_{n,k}(t)/t$. The consecutive comparison always holds $k$ fixed across the two sizes. The uniformity assertions allow $k$ to vary with the old size. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Reviewed extreme-rank argument](https://github.com/ProgramComputer/open-math-research/pull/7) · [Project issue](https://github.com/ProgramComputer/open-math-research/issues/4)

## Cycle-size acceptance in the run encoding

The reviewed encoding identifies $\alpha_{n,p}$ as a probability for a uniform independent color word on $p$ run labels and a uniform permutation of those labels. Write $f(n,p,k)$ for the probability of the run-cycle size restrictions alone. Whenever every color appears in both halves of the word, all upward boundary conditions hold. Thus
$$
0\le f(n,p,k)-\alpha_{n,p}
 \le 2p e^{-\lfloor n/2\rfloor/p}.
\tag{1}
$$
Consider $p$ in any fixed range $c\sqrt{n/\log n}\le p\le b\sqrt n$ with $c,b>0$, and $3\le k\le 11 n/20$. Let $a=kp/n$ and
$$
D=B\left(1+\frac{p\sqrt{k\log n}}n\right),
$$
where $B$ is a sufficiently large absolute constant. Given a cycle of $j$ colors, its word count has distribution $\operatorname{Bin}(n,j/p)$ with mean $\mu=nj/p$. If $j<a-D$, the probability of meeting the threshold is at most $n^{-12}$. If $j>a+D$, the probability of failing it is at most $n^{-12}$. Indeed, set $d=Dn/p$. The Chernoff exponents are at least $d^2/(2k)$ on the low side and $d^2/[2(k+d)]$ on the high side, the latter by monotonicity in $\mu$. The lower bound $d\ge B\sqrt{k\log n}$ controls the quadratic term, and $d\ge Bn/p\gg\log n$ controls the case $d>k$. Increasing $B$ also gives the same bound for the point mass at $k-1$ when $|j-a|>D$.

Let $d(p,L)$ be the probability that a uniform permutation of $p$ labels has all cycle lengths at least the positive integer $L$, with $d(0,L)=1$. A cycle-containing-one decomposition gives
$$
p\,d(p,L)=\sum_{j=L}^p d(p-j,L),\qquad
\frac1{2L}\le d(p,L)\le\frac1L\quad(p\ge L).
\tag{2}
$$
The bounds follow by induction from $d(p,L)=1/p$ for $L\le p<2L$ and $d(p,L)=0$ for $0<p<L$. For $L_+=\max(1,\lfloor a+D\rfloor+1)$ and $L_-=\max(1,\lceil a-D\rceil)$, conditioning on the uniform run permutation and using a union bound over its cycles yields
$$
d(p,L_+)-p n^{-12}\le f(n,p,k)\le d(p,L_-)+p n^{-12}.
\tag{3}
$$
The upper bound with $L_-=1$ is trivial. Since $a\le(11/20)p$ and $D=o(p)$, (1)–(3) give
$$
\alpha_{n,p}\asymp \frac1{1+a}
\tag{4}
$$
uniformly in the stated ranges. For the upper bound this argument also applies when $k$ is any size up to $n$: $L_-$ is comparable to $a$ when $a$ is large, and $d(p,L_-)=0$ when $L_->p$. We will use this upper bound for a conditional residual problem.

## Stability in the number of colors and in the row size

Uniformly in the range in (4),
$$
\frac{\alpha_{n,p+1}}{\alpha_{n,p}}=1+o(1).
\tag{5}
$$
To prove this, it suffices to consider sequences with $a\to\infty$ and sequences with $a$ bounded.

For $a\to\infty$, $D/a=O(1/a+\sqrt{\log n/k})=o(1)$ because $k=an/p\gg\sqrt n$. A threshold increase $L\mapsto L+\delta$ costs at most $\delta/L^2$ whenever $L+\delta<p$. In fact a forbidden cycle of size $j\in[L,L+\delta)$ with all others of size at least $L$ has expected count $d(p-j,L)/j\le1/L^2$ by (2); the case of empty remainder is excluded by $j<p$. Thus (3) differs by a relative $o(1)$ between its upper and lower sides. It follows that $\alpha_{n,p}=d(p,\lceil a\rceil)(1+o(1))$. At fixed $L\ge2$, insertion of a uniform new color in a random permutation of $p$ colors gives
$$
d(p+1,L)=\frac{p\,d(p,L)+d(p-L+1,L)}{p+1}.
\tag{6}
$$
The singleton option spoils an accepted old permutation. Otherwise a unique forbidden cycle of size $L-1$ can be cured by insertion into it, which contributes the second term. The expected count of such cycles with all others accepted is $d(p-L+1,L)/(L-1)$. Formula (6) and (2) give relative change $O(1/p)$. Changing $\lceil a\rceil$ to $\lceil k(p+1)/n\rceil$ costs $O(1/a)$ relatively by the threshold-shift bound. This proves (5) when $a$ grows.

For bounded $a$, couple the permutations by the same uniform insertion, and couple the color words by recoloring each label to the new color independently with probability $1/(p+1)$. Both marginal permutations and words are uniform, and words and permutations are independent. Fix an integer $J$ greater than four times a bound on $a+1$. All cycles of size $>J$ in either row exceed the threshold with probability $1-o(1)$ by Chernoff and the union bound. The singleton insertion has probability $1/(p+1)$ and insertion into a cycle of size at most $J$ has probability at most $J/(p+1)$, by the expected number $1/j$ of $j$-cycles. In all other cases existing small cycles keep their colors and only lose word labels. Conditional on any such small cycle of size $j\le J$, its old count $X$ has binomial point masses bounded by $O_J(\sqrt{p/n})=O_J(n^{-1/4})$, and the expected loss is $nj/(p(p+1))=O_J(\log n)$. A change of acceptance requires loss greater than $M=n^{1/8}$ or $X$ within $M$ of $k$. Its probability is $O_J(\log n/M+M n^{-1/4})=o(1)$. Sum over the expected $O_J(1)$ small cycles. By (1) and (4), this proves (5) in the remaining case.

For consecutive size we have, uniformly when $k\to\infty$,
$$
\frac{|\alpha_{n+1,p}-\alpha_{n,p}|}{\alpha_{n,p}}=o(1/p).
\tag{7}
$$
For the size-only probability append an independent uniform color. If acceptance changes, there is a cycle previously containing exactly $k-1$ labels that receives the new label. A marked cycle of size $j$ has expected count $1/j$ in the run permutation, and it receives the new label with probability $j/p$. Conditional on its existing label count $k-1$, the other labels are uniform over the other colors and the other run cycles are uniform. Therefore
$$
0\le f(n+1,p,k)-f(n,p,k)\le
\frac1p\sum_{j=1}^{p-1}\Pr\{\operatorname{Bin}(n,j/p)=k-1\}
                 f(n-k+1,p-j,k).
\tag{8}
$$
The point masses outside $|j-a|\le D$ total $O(p n^{-12})$. Inside that window $p-j\asymp p$, $n-k+1\asymp n$, and $k(p-j)/(n-k+1)\asymp a$. The upper bound following (4) gives $f(n-k+1,p-j,k)=O(\alpha_{n,p})$ there. If $k>n-k+1$ this conditional probability is zero. The sum of all the point masses in (8) is $O(k^{-1/2}+p/n)$. To see this, the binomial point mass as a function of its probability parameter is unimodal, has integral $1/(n+1)$ by the beta integral, and has maximum $O(k^{-1/2})$ by Stirling because $k/n\le11/20$. A lattice sum at spacing $1/p$ is at most $p$ times the integral plus twice the maximum. Use (1) at both sizes to obtain (7). When $k$ is bounded, (7) follows directly from requiring each color to have at least $k$ labels and to occur in both halves, as the failure probability is exponentially small in $\sqrt n$.

## Front ranks and their exact orientation

Let $c\sqrt{n/\log n}\le h\le3\sqrt n/8$ and normalize the Laurent polynomial as in the fixed-$k$ argument, but divide also by $\alpha_{n,h}$. Set $u_h=(h/(h+1))^n$ and let $z=t/u_h$. The $p$th term's normalized base is
$$
\left[\frac ph\left(\frac h{h+1}\right)^{p-h}\right]^n z^{p-h}.
$$
Both bases at $p=h,h+1$ equal one. Successive terms away from these indices in either direction have ratios at most $q=e^{-5}<.01$, before multiplication by powers of $z$. For $h/2\le p\le2h$, (4) bounds all $\alpha_{n,p}/\alpha_{n,h}$ by a constant. For fixed $p-h$, (5) gives this ratio $1+o(1)$ uniformly. Thus each geometric-tail estimate from the fixed-$k$ calculation is valid with additive error $o(1)$ by dominated convergence. For $p$ outside $[h/2,2h]$ the ratio is $O(n)$, harmless against $(3q)^{h/2-2}$. Rouché on $|z|=1/2$, $|z|=3$ and $|z+1|=1/8$ therefore gives exactly one simple negative rank-$h$ root in $|z+1|<1/8$ and the exact inner and outer disk counts.

At this old root subtract $h E_{n,k}$ from $E_{n+1,k}$ and divide by the same normalization. The $h+1$ term from $(p-h)\alpha_{n,p}/\alpha_{n,h}$ is $z(1+o(1))$, at most $-7/8+o(1)$, and the other such terms have summed absolute bound $3s/(1-s)^2+2s/(1-s)+o(1)<.11+o(1)$ for $s=.02$, by the same domination. The terms with $p(\alpha_{n+1,p}-\alpha_{n,p})/\alpha_{n,h}$ are $o(1)$ by (7) on $[h/2,2h]$ and exponentially small outside. Thus the value of $P_{n+1}$ at the old rank-$h$ root has sign $(-1)^h$. The old modulus after scaling by $u_{n+1,h}$ lies in $(7/8,9/4)$ inside the new rank-$h$ annulus $(1/2,3)$. The $h-1$ inner roots contribute sign $(-1)^{h-1}$ before this new root even if some inner roots are complex: nonreal roots come in conjugate pairs, and no positive root can occur because all coefficients are nonnegative and the constant coefficient is one. This fixes the strict consecutive order for rank $h$. Choosing $c$ smaller than the coefficient in the reviewed uniform growing-rank theorem fills every smaller rank as well.

The absolute front-to-pole interface remains $h_*=\lfloor7\sqrt n/20\rfloor$. For ranks $h_*,h_*+1$, the phase $(n+1)\arctan(\pi/s)/\pi$ at the isolated root is between $h+0.45$ and $h+0.55$ for large $n$. This follows from $s=n\log(1+1/h)+O(.14)$, the reciprocal-log expansion, and the phase derivative tending to $(7/20)^2$. The interface lies at $s\sim(20/7)\sqrt n<3\sqrt n$.

## A near-pole contour for growing k

Assume now $k\to\infty$ and $k\le C_0 n/\log n$ with fixed $C_0>0$. On $-1\le t<0$ write $t=-e^{-s}$, $w=(1-t)z$, $w_p=s+ip\pi$ for odd $p$, $r=|w_1|$, $\theta=\arg w_1$ and $S=\sin\theta$. The normalized cycle EGF is
$$
\frac{T_s(w)}{1+e^{w-s}},\qquad
T_s(w)=\exp\left(aw-\sum_{\ell=2}^{k-1}
\frac{t A_{\ell-1}(t)}{(1-t)^\ell\ell!}w^\ell\right),
\quad a=\frac{e^{-s}}{1+e^{-s}}.
$$
This follows from the ordinary Eulerian EGF and removal of short cycles, including the singleton factor $e^{-z}$. The leading pole pair in $E_{n,k}$ has positive amplitude and phase $\Psi_n=(n+1)\theta-\gamma(\theta)$, with $\gamma=\Im\log T_s(w_1)$ using the displayed polynomial exponent. This phase is the one in the fixed-$k$ proof. We need $0\le s\le3\sqrt n$, as the preceding absolute interface lies inside this range.

For the coefficients of $\log T_s$ there are two complementary exact forms. The partial fractions of the Eulerian power sum give, for $\ell\ge2$,
$$
\frac{t A_{\ell-1}(t)}{(1-t)^\ell\ell!}w^\ell
=\frac1\ell\sum_{p\ {\rm odd}}(w/w_p)^\ell .
\tag{9}
$$
For $s>0$ the equivalent geometric expansion, including the linear coefficient, is
$$
\log T_s(w)=-\sum_{m\ge1}\frac{(-e^{-s})^m}{m}
                         \sum_{\ell=1}^{k-1}\frac{(mw)^\ell}{\ell!}.
\tag{10}
$$
Both follow from the same Eulerian power-sum identity. For (9), differentiate the hyperbolic-tangent partial fractions, which removes its constant term. At an odd pole $w_p$, (10) yields the especially useful identity
$$
\log T_s(w_p)=-\log(1+e^{-s})-\sum_{m\ge1}\frac{Q(k,mw_p)}{m},
\qquad Q(k,x)=e^{-x}\sum_{\ell=0}^{k-1}\frac{x^\ell}{\ell!}.
\tag{11}
$$
Indeed $e^{mw_p}=(-1)^m e^{ms}$. This is an identity of exponents with no integer ambiguity in their imaginary parts.

Fix $A=100(C_0+1)$, and choose a small constant $c_1>0$ depending only on $A,C_0$. Set $R_{\max}=r(1+2A/k)$. We show
$$
\sup_{|w|\le R_{\max}}|\log T_s(w)|\le20\log k+O(1),
\tag{12}
$$
with constants depending only on $C_0,A,c_1$. In the compact range $s\le10$, use (9), $S^2>2/25$, and $\sum_p|r/w_p|^2<20$. The last bound follows from $p^2-1\ge8p^2/9$ for $|p|\ge3$ and $\sum_{p\ge3}p^{-2}\le1/2$. Also
$$
\sum_{1\le \ell<k}\frac{e^{2A\ell/k}}{\ell}
\le \log k+O_A(1),
$$
since $e^{2A\ell/k}-1\le 2Ae^{2A}\ell/k$. The linear term is bounded in the compact range.

If $10\le s\le c_1\sqrt k$, split the log coefficients at $\ell=\lceil s^2\rceil$. For the upper part, $\ell S^2\ge c>0$ and Bernoulli's inequality in (9) gives $\sum_p |r/w_p|^\ell\le3$. For example $\ell S^2>8$ for $s\ge10$, so the far-pole sum is less than $2\sum_{p\ge3}1/[4(p^2-1)]<1$. This upper part is at most $3\log k+O_A(1)$. For the lower part use (10). With $c_1$ sufficiently small that $A c_1^2<1/4$, we have $R_{\max}-s\le6/s$. If $m\le4s$, bound the sum of the Poisson terms of mean $mR_{\max}$ by its full exponential. The resulting contribution is at most
$$
\sum_{m\le4s}\frac{e^{6m/s}}m \le \log(1+s)+O(1),
$$
by subtracting one from each exponential and bounding the difference by $6e^{24}m/s$. For $m>4s$, a Poisson variable of mean $mR_{\max}>4s^2$ has probability at most $e^{-mR_{\max}/8}$ of being below $\lceil s^2\rceil$. Multiplying by $e^{m(R_{\max}-s)}$ leaves at most $e^{-sm/20}$ since $s\ge10$. This proves (12) in the second range.

If $c_1\sqrt k\le s\le10k$, use (10) without a split in $\ell$. For $m\le M=\lceil4k/s\rceil$, we have $(R_{\max}-s)M=O_{A,c_1}(1)$, because $r-s\le\pi^2/(2s)$, $s^2\ge c_1^2 k$ and $M\le14k/s$. As above, the sum of $e^{m(R_{\max}-s)}/m$ is at most $\log(1+k/s)+O_{A,c_1}(1)$. For $m>M$, the Poisson mean is greater than $4k$, and its lower-tail bound combined with $(R_{\max}-s)/s=O_{A,c_1}(1/k)$ gives $O(e^{-sm/20}/m)$. This proves (12) and the sharper exponent bound with coefficient one on $\log(1+k/s)$ in the third range. Finally when $s\ge10k$ every Poisson mean is at least $10k$. The same estimate at every $m$ gives $|\log T_s(w)|=O(e^{-cs})$ on the disk for some absolute $c>0$. All estimates apply at $w_1$ as well, giving $|T_s(w_1)|\gtrsim k^{-20}$.

Choose the coefficient contour at radius $R=r(1+A/k)$ for $s\le c_1\sqrt k$. It encloses just the principal pair: $|w_3|/r-1\ge2\pi^2/r^2>2A/k$ for $c_1$ small and $k$ large. Its distance to all poles is at least $Ar/k$. For $s>c_1\sqrt k$, choose any radius in $[r(1+A/k),r(1+2A/k)]$ at distance at least $n^{-2}$ from every pole radius. Only $O(\sqrt n)$ poles can be near this interval and its length is $\gtrsim n^{-1}$, so such a radius exists. In either case $|1+e^{w-s}|^{-1}=O(n^2)$ on the chosen circle, since distance $\delta$ from the odd poles bounds it by $O(1/\min(1,\delta))$ by the elementary cosine and reverse-triangle estimates. On using the principal pole amplitude to normalize the coefficient, (12) bounds the circle contribution by
$$
O\bigl(r\,n^2 k^{40}(1+A/k)^{-n}\bigr)=o(n^{-1/2})=o(S).
\tag{13}
$$
Indeed $(1+A/k)^{-n}\le\exp(-An/(2k))\le n^{-A/(2C_0)}$ for large $k$, $r=O(\sqrt n)$ and $k\le n$ eventually. The same contour is valid for the next size at the same $s,k$.

## Discrete Poisson derivative at nearby poles

It remains to compare the included pole amplitudes when $c_1\sqrt k\le s\le10k$. For $|w_p|\le R_{\max}$ we have $|\Im w_p|\le C_{A,c_1}s/\sqrt k$. On the vertical segment joining $s$ to such a pole, the derivative of the complex sum in (11) is
$$
-\sum_{m\ge1}\frac{e^{-mw}(mw)^{k-1}}{(k-1)!}.
$$
Its modulus is at most
$$
\left(\frac{|w|}{s}\right)^{k-1}
\sum_{m\ge1}\frac{e^{-ms}(ms)^{k-1}}{(k-1)!}
=O_{A,c_1}(1/\sqrt k).
\tag{14}
$$
The prefactor is bounded by the vertical-segment bound. The real summand is the gamma density of shape $k$ sampled at spacing $s$. It is unimodal, has integral one, and has maximum $O(k^{-1/2})$ by Stirling. The sum is therefore $O(k^{-1/2}+1/s)=O_{c_1}(k^{-1/2})$. Consequently
$$
\left|\log T_s(w_p)-\log T_s(w_1)\right|
\le C_{A,c_1} (|p|+1)/\sqrt k .
$$
This tends uniformly to zero for each fixed included $p$. For all included $p$ it is $O_{A,c_1}(1)$ because $|p|/\sqrt k=O_{A,c_1}(s/k)$ and $s\le10k$.

For the exact coefficient comparison, normalize the row by the positive principal-pair amplitude so that it is $Y_n=\cos\Psi_n+$ distant pole terms $+o(S)$. For $s\le3\sqrt n$, the weighted unrestricted pole envelope satisfies
$$
\sum_{p=3,5,\ldots}p\,|r/w_p|^{n+1}<1/10
$$
for $n\ge100$, since $nS^2\ge1$ for $n\ge100$ in this range, by the rational estimate in the [fixed-threshold comparison](fixed-threshold.md). The envelope is dominated by a summable sequence independent of $n$. In the low-$s$ regime the chosen circle encloses no distant pole, and for $s\ge10k$ the short-cycle factors are uniformly $1+o(1)$. In the remaining regime the amplitude ratios are uniformly bounded and converge to one at each fixed included pole by (14). Split the weighted sum at a sufficiently large fixed pole index to conclude that its version including the amplitude ratios is below $11/100$ uniformly for all sufficiently large $n$.

The exact next-row subtraction has leading part $-S\sin\Psi_n$ and a distant pole multiplier satisfying
$$
|r/w_p-\cos\theta|\le pS.
$$
In fact division by $S$ gives $|\pi^2-isp\pi|/(\pi|s+ip\pi|)\le p$. The contour errors in both rows are $o(S)$ by (13), so
$$
|Y_n-\cos\Psi_n|<1/4,\qquad
|Y_{n+1}-\cos\theta\,Y_n+S\sin\Psi_n|<S/4
\tag{15}
$$
uniformly. These are sufficient for both the integer phase signs and the adjacent signs at old roots.

## Phase and completion in the pole regime

On $s\ge c_1\sqrt k$, (11) and (14) give $|\gamma|=O(1/\sqrt k)$ by comparing vertically to the real point $s$, and $|d\gamma/ds|=O(1/\sqrt k)$ by differentiating at $w_1=s+i\pi$. If $s\ge10k$, use directly (11) and the pointwise gamma-density tail for $ms\ge10k$, obtaining exponentially small bounds instead. Since $|(n+1)d\theta/ds|=(n+1)\pi/(s^2+\pi^2)$ has a positive lower bound on $s\le3\sqrt n$, the main phase is strictly monotone here.

For $s\le c_1\sqrt k$ the truncated partial fractions in (9) give $|d\gamma/d\theta|=O((1+s)^2\log(2+s))$ uniformly. The $p=1$ factor is constant, the $p=-1$ derivative is a finite geometric sum of size $O(1/S)$, and for the other poles put $v_p=w_1/w_p$. Then $|v_p'|=|p-1|/[1+(p^2-1)S^2]$ and
$$
\sum_{\ell=2}^{k-1}|v_p'v_p^{\ell-1}|
\le \frac{C}{|p|S^2\sqrt{1+c p^2S^2}} .
$$
Summing for $|p|\le1/S$ and $|p|>1/S$ proves the claimed bound. The linear term's imaginary part is $\pi a$ and also has bounded $\theta$ derivative. Since $k\log k\le C_0 n$ eventually, choosing $c_1$ sufficiently small makes the derivative less than $(n+1)/2$ for large $n$, after handling bounded $s$ directly. This proves strict phase monotonicity across the whole bulk. At $s=0$ the phase is $n\pi/2$ because the odd Eulerian terms beyond the linear term vanish at $t=-1$, and the even terms are real.

At the front cross-section $s\sim(20/7)\sqrt n$ the correction is $o(1)$, since this lies in $s\ge c_1\sqrt k$. Thus the corrected integer level $h_*+1$ has exactly $h_*$ roots of smaller modulus. Apply (15) at the continued integer levels through $\lfloor n/2\rfloor$. The sign intervals give at least $\lfloor n/2\rfloor-1$ roots of modulus below one, and reciprocity gives the same number above one. If $n$ is odd, reciprocity supplies the central zero at $-1$. These account for all $n-2$ nonzero roots. Monotonicity puts every old middle root of rank $h$ at a phase between $h\pi$ and $(h+1)\pi$. At that old root (15) gives the new $E_{n+1,k}$ sign $(-1)^{h+1}$, hence the $P_{n+1}$ sign $(-1)^h$. At the central root in odd size the same conclusion follows at $\Psi_n=n\pi/2$. The front signs were already proved, and the remaining signs follow by reciprocity of degree $n-2$ for $P_n$ and degree $n-1$ for $P_{n+1}$. These signs give strict consecutive interlacing.

We proved this for every sequence $k\to\infty$ in the specified range. Sequences with bounded $k$ have a subsequence of constant $k$, covered by the fixed-threshold pole proof. The sequential criterion therefore gives the asserted uniform cutoff in $n$ for all $3\le k\le C_0 n/\log n$.

## Consecutive bulk signs at large minimum cycle length

Let $F_{n,k}(\theta)=r^n E_{n,k}(t)/(n!(1-t)^n)$, $t=-e^{-s}$, $r=(s^2+\pi^2)^{1/2}$, $S=\sin\theta=\pi/r$, $z_p=(\cos\theta+ipS)^{-1}$ for odd integers $p$. Let $d_n$ denote the probability that a random permutation has only cycles of length at least $k$. In particular $d_n\ge1/n$. For all large $n$, uniformly for $k\ge 100 n/\log n$ and $nS^2\ge1$, we prove:
$$
 \big|F_{n,k}/(2d_n)-\cos(n\theta)\big|<1/4,\quad
 \big|F'_{n,k}/(2n d_n)+\sin(n\theta)\big|<1/4.
$$
Throughout $0<\theta\le\pi/2$. The derivative is in $\theta$. Moreover, at each zero of $F_{n,k}$ in this range the new row has the sign of $-\sin(n\theta)$.

The cycle expansion in [the cycle expansion](linear-cutoffs.md) splits $F_{n,k}=d_n\sum_p z_p^n+M$, where $M$ sums all assignments with at least two different pole indices. Put $P=\sum_p|z_p|^{k-1}$ and $P_1=\sum_p(1+|p|)|z_p|^{k-1}$. For $k\ge12$, Bernoulli's inequality with a fourth-power tail gives $P=O(1+1/(S\sqrt k))$ and $P_1=O(1+1/(k S^2))$ whenever $nS^2\ge1$. Indeed for $p\ge3$ we can use $(1+c k p^2 S^2)^{-2}$ as a majorant and split the sum at $p=1/(S\sqrt k)$, handling the two principal poles separately. Put $D=n/k\le(\log n)/100$. Thus $P=O(1+\sqrt D)$, $P_1=O(1+D)$, and $\exp(2\sqrt{PD})=\exp(O((\log n)^{3/4}))=n^{o(1)}$. The absolute mixed sum bound from [the cycle expansion](linear-cutoffs.md) is $O(P^2\exp(2\sqrt{PD})/(k^2 S))=n^{-3/2+o(1)}=o(d_n)$.

For the differentiated mixed sum we claim $|M'|\le n^{-1/2+o(1)}=o(n d_n)$. Use the same first pair of distinct pole indices $p,r$ and the same summation by parts over their admissible lengths $a,b-a$. If the derivative hits either of the distinguished slots, the factor is $a z'_p/z_p$ or $(b-a)z'_r/z_r$. The resulting weight after stripping off the derivative ratio is $1/(b-a)$ or $1/a$, so its supremum plus total variation is at most $2/k\le2n/k^2$. The derivative ratio costs $|z'_p/z_p|\le(1+|p|)$, since $|\sin\theta-ip\cos\theta|\le1+|p|$ and $|z_p|\le1$. The telescoping denominator and the factors $|z_p z_r|^{k-1}$ are unchanged. A differentiated outside slot of length $c_i$ instead costs at most $c_i(1+|p_i|)\le n(1+|p_i|)$, leaving the original variation estimate on the distinguished pair. There are at most $D$ slots. Summing over poles with one weight $1+|p|$ bounds each term sum by $P_1 P^{\ell-1}$ in place of $P^\ell$. The same length and factorial bounds as in the original argument then give
$$
 |M'|\ll\frac{n D P_1 P}{k^2 S}\exp(2\sqrt{PD})=n^{-1/2+o(1)}.
$$
Differentiation is justified at each fixed $\theta>0$ by summable majorants of these differentiated pole series (and finitely many cycle types). For the common-pole sum the conjugate pair $\pm1$ gives $2\cos(n\theta)$, with derivative $-2n\sin(n\theta)$. Each remaining positive odd $p$ costs at most $|z_p|^n$ in the half sum, or $p|z_p|^{n+1}$ after differentiation and division by $n$, since $|z'_p|\le p|z_p|^2$. Both sums are below $1/10$ by the weighted bound in [the fixed-threshold proof](fixed-threshold.md) ($nS^2\ge1$). This proves the two bulk bounds.

At an old root the maximum-insertion recurrence gives the exact identity
$$
 (n+1)F_{n+1,k}=S F'_{n,k}+\left(\sum_p z_p^k\right)F_{n+1-k,k}.
$$
This uses $t\,d\theta/dt=\pi/r^2$; differentiating the normalization produces only multiples of the vanishing old polynomial. If $1\le m=n+1-k<k$, the last term vanishes. For $m\ge k$ the absolute cycle expansion gives $|F_{m,k}|\le (P/k)\exp(2\sqrt{PD})$. In fact, with $\ell$ slots the first $\ell-1$ lengths have at most $n^{\ell-1}/(\ell-1)!$ choices, the last is determined, and each slot costs at most $P/k$. Summing after division by $\ell!$ gives the bound. Thus the lag has size at most $P^2\exp(2\sqrt{PD})/k=n^{-1+o(1)}=o(n S d_n)$. At the old root, $|\cos(n\theta)|<1/4$; the derivative has magnitude greater than $n d_n$ and sign $-\operatorname{sgn}\sin(n\theta)$. This proves the asserted next-row sign. The estimate supplies the entire middle together with the front ranks already treated above.


## Completion for all minimum cycle lengths

Set $C_0=100$. The intermediate range was proved above. For $100n/\log n\le k\le11n/20$, let $h_*=\lfloor7\sqrt n/20\rfloor$ as in the front proof. In this range the principal phase is $n\theta$. Its difference from $(n+1)\theta$ at the front interface is $O(n^{-1/2})$. Hence the sample $n\theta=(h_*+1)\pi$ separates ranks $h_*$ and $h_*+1$ with their known absolute counts. It satisfies $nS^2\ge1$ since $7\pi/20>1$. Every subsequent lower-half sample does as well. The bulk signs and reciprocity therefore exhaust the degree. At each old bulk root of rank $h$ the old phase is between $h\pi$ and $(h+1)\pi$, including the central root at odd size. The derivative comparison gives sign $(-1)^{h+1}$ for the new row, and the front and reciprocal signs complete the strict consecutive comparison. Finally, when $k>11n/20$ and $n$ is sufficiently large, both $n$ and $n+1$ are less than $2k$. Only single cycles occur, and the nonzero-root polynomials are $A_{n-1}$ and $A_n$. The Eulerian recurrence gives their strict interlacing by the alternating signs of the derivative at the simple negative old roots.

Consequently there is one absolute $N$ such that the assertion holds for all $n\ge N$ and every $3\le k\le n$. This leaves only finitely many pairs in the original two-parameter conjecture. The argument does not identify a numerical $N$ or certify the remaining finite set.

## Scope and priority

This argument uses the established exact run encoding, the labelled-cycle Eulerian expansion, and the previously reviewed growing-extreme theorem. Its new uniform steps are the acceptance estimates, the truncated-Poisson representation of pole amplitudes, and their use in the near-pole contour. Literature checks on November 25, 2026 used the original statement and indexed GitHub and X queries by Alexandersson, “excedance polynomials”, “minimum cycle length”, “cycles of length at least”, “no 2-cycles”, “real-rooted” and “interlacing”. The independent public investigation records a lagged recurrence obstruction and finite evidence. No competing uniform eventual theorem was found in the sources checked. Indexed X coverage was limited. [Primary statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Independent public issue](https://github.com/1337isnot1337/solved-conjectures/issues/81) · [Project issue](https://github.com/ProgramComputer/open-math-research/issues/4)
