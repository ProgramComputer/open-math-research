# A uniform middle-root bound by signed pole sums

Fix $3\le k\le n$. Let $P_n=E_{n,k}/t$ for the excedance polynomial with minimum cycle length $k$, and let $L$ be the distinguished-cycle term in the insertion recurrence. For $n\ge3k-1$, put $t=-\exp(-\pi\cot\theta)$ and $S=\sin\theta$. At every real old root in the middle interval

$$
nS^2\ge6/5,\qquad kS\ge2000,
$$

both insertion signs preserve the derivative's sign. The old row also has the alternating signs at integer samples in this interval. There is no upper bound on the number of cycles.

Combined with the established exterior theorem, this gives strict interlacing whenever $n\ge10{,}000$ and $k\ge2000\sqrt n$. Combining with the short-cycle range gives strict interlacing for every $k$ at $n\ge10^{18}$. The unrestricted conjecture remains open in the finite complement. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)

**Formal verification**　⬜ None. An independent agent checked the proof and replayed the finite-pole identity and derivative in Gaussian-rational arithmetic. [Independent review](uniform-hilbert-independent-review.md) · [Scalar checker](check-uniform-hilbert-poles.py) · [Prior-art check](literature.md)

## Setup and a pole moment bound

Take $0<\theta\le\pi/2$ and write $C=\cos\theta$, $z_p=(C+ipS)^{-1}$, $\rho_p=|z_p|$, for odd integers $p$. Use $F_j=r^j E_{j,k}(t)/(j!(1-t)^j)$ with $r=\pi/S$, and $B_j=\sum_pz_p^j$. The exact product is $\sum_jF_j u^j=\prod_p D(z_pu)$, where

$$
D(u)=\sum_{j\ge0}d_j u^j
=\exp\left(\sum_{j\ge k}u^j/j\right).
$$

The cycle probabilities obey $1/(2k-1)\le d_j\le1/k$ for $j\ge k$. Put $b_s=[u^s](1-u)(D(u)-1)$, so $\sum_s|b_s|<2/k$. Let $R_j=F_j-d_jB_j$. Put $m=n+1-k$. Either output index $M=n,m$ has $M\ge2n/3$, hence $MS^2\ge4/5$. Below $A=kS\ge2000$. [Pole and variation inputs][poles] · [Variation proof][var]

For any real $\ell\ge4$, write $\lambda=\ell S^2$. Bernoulli's inequality gives $\rho_p^\ell\le (1+(2/9)\lambda p^2)^{-2}$ for $|p|\ge3$. Integrating the decreasing unweighted envelope and the unimodal weighted envelope along the positive odd lattice gives

$$
\sum_p\rho_p^\ell\le2+2/\sqrt\lambda,
\qquad
\sum_p |p|\rho_p^\ell\le2+2/\sqrt\lambda+3/\lambda.
$$

Indeed for $c=2\lambda/9$, the integral of $(1+cp^2)^{-2}$ over $[0,\infty)$ is $\pi/(4\sqrt c)$. For the weighted moment use $\int_0^\infty p(1+cp^2)^{-2}dp=1/(2c)$ and $max_{p\ge0}p(1+cp^2)^{-2}<1/(3\sqrt c)$. For each positive odd lattice the sum of a nonnegative unimodal envelope is bounded by its maximum plus half its integral. Keep the two principal poles separately.

## Signed sums when $kS^2\le1/4$

This regime has $C>0$, $-\log C\le1/(4k)$, and $\sqrt k\ge2A$. First obtain exponential moments of the numerator sequence. For $s>k$, the recurrence for $d_s$ implies

$$
s b_s=-\sum_{i=s-k+1}^{s-1}b_i .
$$

The first block $k<s\le2k$ has $|b_s|\le1/k^2$, since $d_s=1/s$ for $k\le s<2k$ and the jump at $2k$ is $(1/k-1/(2k-1))/(2k)$. For later blocks let $M_j=\max_{jk<s\le(j+1)k}|b_s|$. The recurrence gives $M_j\le\max(M_{j-1},M_j)/j$, hence $M_j\le1/(j!k^2)$. Adding $b_k=1/k$ gives, for $c\ge0$,

$$
\sum_s |b_s|e^{cs/k}\le\frac{e^{c+e^c}}k,
\qquad
\sum_s s|b_s|e^{cs/k}\le e^{c+e^c}(1+e^c).
$$

For $c=1/2$ these are below $9/k$ and $27$. Cauchy–Schwarz also bounds the corresponding square-root moment by $16/\sqrt k$.

For distinct poles $a,q$ put

$$
A_{a,q}(u)=\sum_{s\ge k}\frac{b_s z_q^{s-1}u^s}{i(q-a)S},
\qquad
Q_a(u)=\prod_{q\ne a}(1+A_{a,q}(u)).
$$

Expanding by occupied pole sets and using partial fractions of the geometric denominators gives the exact coefficient identity

$$
R_M=[u^M]\sum_a (D(z_au)-1)(Q_a(u)-1).
$$

For a fixed occupied set, partial fractions select $a$ and contribute $(1-z_q/z_a)^{-1}$ for each other $q$. Since $(1-z_q/z_a)^{-1}=z_q^{-1}/[i(q-a)S]$, this is exactly the displayed product for that $a$. All calculations can take place in series modulo $u^{M+1}$. Each coefficient and its angular derivative has locally absolutely convergent pole sums because $k\ge2000$ here.

Use the norm $\|f\|=\sum_{s=0}^M |[u^s]f|e^{s/(4k)}$ in that truncated algebra. To estimate the linear term in $\log Q_a$, the following signed kernel bound is important. For any complex finite measure representing a sequence as $f_q=\int e^{-iqx}d\mu(x)$, if its signed sum converges absolutely then

$$
\left|\sum_{q\ne a}\frac{f_q}{q-a}\right|
\le\frac\pi2\|\mu\|_{\mathrm{TV}}.
$$

To prove it write $q=a+2j$ and insert a factor $\eta^{|j|}$ with $0<\eta<1$. The paired sum is $-i\sum_{j\ge1}\eta^j\sin(2jx)/j$. Its magnitude is at most $\pi/2$ by the imaginary part of $-\log(1-\eta e^{2ix})$. Integrate and let $\eta$ increase to one. For $f_q=z_q^s$, the Laplace formula represents it by a measure of total variation at most $C^{-s}$, namely the Fourier image of the gamma density of shape $s$ and unit scale under $x\mapsto Sx/C$, multiplied by $C^{-s}$. Therefore $\|\sum_{q\ne a}A_{a,q}\|\le(\pi/2)(9/A)<15/A$. Here $e^{s/(4k)}C^{1-s}\le e^{s/(2k)}$. An absolute sum at this linear step would introduce a factor growing as $\log(n/k)$.

The individual norms satisfy $\|A_{a,q}\|\le9/(A|q-a|)$, and $\sum_{q\ne a}|q-a|^{-2}<1$. With $\delta=9/(2A)$, the total higher terms in the logarithm have norm at most $81/(2A^2(1-\delta))<41/A^2$. Thus $\|\log Q_a\|<16/A$ and $\|Q_a-1\|<17/A$.

For the derivative, $z_q'/z_q=(z_q-C)/S$. The sequence $z_q^{s+1}-Cz_q^s$ has a Fourier measure with variation bounded by $C^{-s-1}(S^2+1/\sqrt s)$. Indeed in the common gamma density of shape $s$, the difference of the two measures is the density times $x/s-C^2$, with the overall factor $C^{-s-1}$. If $X$ is gamma with shape $s$ and unit scale, $\mathbb E|X/s-1|\le1/\sqrt s$. Thus the derivative of $z_q^s$ has a representing measure of norm at most $C^{-s-1}(sS+\sqrt s/S)$.

The derivative norm of the linear logarithm, divided by $M$, is therefore at most

$$
\frac\pi2\left(\frac{27}{M}+\frac{16}{\sqrt k\,MS^2}+\frac9{kMS^2}\right)<16/A .
$$

This includes differentiation of $1/S$. For each individual derivative, bound the Fourier integral by the variation of the representing measure before summing over $s$. This gives the same parenthetical expression with $1/|q-a|$ in place of $\pi/2$. Since $MS^2\ge4/5$, $M\ge k$, and $\sqrt k\ge2A$, the expression is at most $10/A+(27/4+45/16)/A^2<11/A$. Thus each individual normalized derivative has norm below $11/(A|q-a|)$. The derivative of the higher logarithm terms has norm, after division by $M$, at most $99/(A^2(1-\delta))<100/A^2$. The derivative of the exponential now gives $\|Q'_a\|/M<17/A$.

To sum over $a$, split at total non-distinguished numerator degree $T=M/2$. When $T\le M/2$, the degree of $D(z_a u)-1$ is at least $M/2$, retaining $\rho_a^{M/2}$ and $|a|\rho_a^{M/2}$ for the derivative of that factor. The two pole moments are below six and thirteen. When $T>M/2$, retain $\rho_a^k$ and $|a|\rho_a^k$ and use the norm weight penalty $e^{-M/(8k)}$. With $x=M/k\ge1$, the unweighted pole moments are bounded by $(9/2)\sqrt x$ and $(33/4)x$. Multiplying by $e^{-x/8}$ and adding the short-degree bounds gives respective bounds below twelve and thirty-eight. The short and long coefficient restrictions occur only after the product norm, which preserves the signed cancellation when the coefficients are collected at each fixed $T$. As $d_j\le1/k$, we conclude

$$
k|R_M|<204/A,\qquad k|R'_n|/n<850/A .
$$

The derivative sum uses thirty-eight for the distinguished-factor derivative and twelve for $Q'_a$.

## Absolute sums when $kS^2\ge1/4$

Use the partial-fraction method of the [separated-pole argument][poles]. Retain powers $w_p=\rho_p^{k/3-1}$ at every occupied pole and a power $\rho_b^{M/(3h)}$ at one occupied pole $b$ that carries at least $M/h$ out of the $M$ allocated powers. For $h$ occupied poles, the resulting denominator factors are $S^{1-h}\prod_{q\ne a}|q-a|^{-1}$. Here $\sum_p w_p\le10$ by $(k/3-1)S^2\ge1/16$. Uniformly in $a$, sum $w_q/|q-a|$ first over $|q-a|\le6$ and then over $|q-a|\ge8$. These two parts total at most $U=11/6+10/8<4$. Thus this slab does not require the growing pole-width estimate.

Write $V_h=\sum_b\rho_b^{M/(3h)}\le2+4\sqrt h$, using $MS^2\ge4/5$. In particular $V_2<8$ and $V_h\le6h$. For a fixed distinguished partial-fraction pole $a$ and largest-power choice $b$, the remaining poles sum by elementary-symmetric bounds with the factorial $(h-1)!$ if $a=b$, and $(h-2)!$ if $a\ne b$. In the latter case summing $a$ using $w_a/|a-b|$ costs a further factor $U$. Thus the sum of both choices, omitting $S^{1-h}$, is at most $hV_h U^{h-1}/(h-1)!$. The numerator mass for each pole is below $2/k$.

In the derivative, the reserved extra $e_p/3$ powers at every pole, where $e_p$ is its assigned exponent, bound the normalized power derivative cost by $9h/4$. For nonprincipal $p$ this follows from $e_p|p|\rho_p^{1+e_p/3}/n\le6|p|/[n(p^2-1)S^2]\le9/4$. The differentiated denominators add at most $(h-1)/(nS)$. Hence the overall normalized derivative cost is at most $5h/2$. With $\eta=8/A$ the two absolute estimates become

$$
k|R_M|\le2\sum_{h\ge2}\frac{hV_h\eta^{h-1}}{(h-1)!},
\qquad
k|R'_n|/n\le5\sum_{h\ge2}\frac{h^2V_h\eta^{h-1}}{(h-1)!}.
$$

Keep the $h=2$ term separately, with $V_2<8$. For $h\ge3$ use $h^2\le9\cdot3^{h-3}$, $h^3\le27\cdot3^{h-3}$ and $(h-1)!\ge2$. The resulting rational bounds are $k|R_M|<13/100$ and $k|R'_n|/n<65/100$. The small-slab estimates also imply these two bounds.

## Old-root comparison and effective consequences

At $nS^2\ge6/5$, the old nonprincipal single-pole value and normalized derivative tails are below $1/50$ and $1/16$. The exact checker bounds $\rho_p^n$ by $(1+(p^2-1)/160)^{-96}$ and uses a first-moment integral beyond nine. Together with $2kd_n>1$, the total value error relative to the principal cosine, multiplied by $k$, is below $15/100$. This proves the integer sample signs. At every old root it gives $|\sin(n\theta)|>98/100$, and

$$
k|F'_n|/n>98/100-65/100-1/16>1/4 .
$$

At an old zero the common insertion normalization compares $SF'_n$ with $B_kF_m$ as in the existing proof. The pole moments give $k|F_m|<22/5$ and $|B_k|/(nS)\le4/A$. Thus $k|B_kF_m|/(nS)<1/100$, proving the strict comparison for both signs.

For $n<3k-1$ the [one- and two-cycle theorem][two] already applies. Otherwise, assume $n\ge10{,}000$ and $k\ge2000\sqrt n$. The [exterior theorem][front] isolates the first $H=\lfloor7\sqrt n/20\rfloor$ roots in modulus and proves the insertion comparison at them. They precede the same sample of index $H+1$ used in the [earlier join][join], where $nS^2>6/5$ and therefore $kS>2000$. The middle samples alternate from that index to the midpoint and by reciprocity to index $n-H-1$. The $n-2H-2$ middle gaps and $2H$ exterior roots exhaust the old degree $n-2$. At every old root both pencils have the derivative sign. The leading and constant coefficients are one for both next pencils, so the consecutive old-root gaps and both outside intervals exhaust the next degree $n-1$.

For $n\ge10^{18}$, every other $k<2000\sqrt n$ satisfies the [short-cycle condition][short] $n/(200k)>30\log n+20$. Indeed $\sqrt n/400000>30\log n+20$ at $10^{18}$. For $v=\log n$, the logarithmic derivative of $e^{v/2}/(30v+20)$ is $1/2-30/(30v+20)>0$ thereafter. This gives the claimed effective height for actual consecutive rows. With the existing [three-cycle range][three] and the all-size $k=3$ result, any remaining counterexample has $k\ge4$, $4k\le n<10^{18}$ and $k<2000\sqrt n$, outside the short-cycle sufficient condition.

Both checks run with the Python standard library. The independent replay compares the finite-pole identity and its derivative in Gaussian-rational arithmetic for two pole sets in degrees 1 through 20. [Scalar checker](check-uniform-hilbert-poles.py) · [Scalar replay](uniform-hilbert-poles-output.txt) · [Independent replay checker](check-uniform-hilbert-identity.py) · [Independent replay output](uniform-hilbert-identity-output.txt)

[poles]: ../separated-poles.md
[var]: ../cycle-probability-variation.md
[front]: ../effective-front.md
[short]: ../effective-uniform.md
[two]: ../two-cycle-band.md
[three]: ../three-cycle-complete.md
[join]: ../effective-threshold.md
