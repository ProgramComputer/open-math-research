# Differentiated residues for large ratios of size to threshold

Let $E_{n,k}(t)$ count permutations of $[n]$ by excedances with all cycles of length at least $k$, and put $P_n(t)=E_{n,k}(t)/t$. On the first half of the negative axis put $t=-\exp(-\pi\cot\theta)$, $S=\sin\theta$ and $C=\cos\theta$. Assume

$$
n/k\ge50,\qquad kS\ge3,\qquad kS^2\le1/25,\qquad nS^2\ge6/5.
$$

The integer-phase samples have alternating signs in this interval. At every old root there, the derivative term in the insertion recurrence strictly dominates the lag. Both insertion signs therefore have the derivative's sign. The statement has no upper bound on $n/k$ or on the number of occupied poles. Together with the adaptive table and short-cycle circle bounds, it gives simple negative roots and strict consecutive interlacing with the actual next row for every threshold $3\le k\le n$ at old size $n\ge1{,}408{,}334$. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)

**Formal verification**　⬜ None. An independent agent checked the written argument and reproduced the scalar estimates with distinct bounds. [Review](review-wide-differentiated-residue.md) · [Prior-art check](literature.md)

## Uniform coefficient majorants

Use the [Eulerian pole expansion and signed-pole identities](../uniform-hilbert/README.md). Write $A=kS$, $z_a=(C+iaS)^{-1}$, $\rho_a=|z_a|$ for odd $a$, $B_j=\sum_a z_a^j$, $r_0=\pi/S$, and $m=n+1-k$. Set $F_N=r_0^N E_{N,k}(t)/(N!(1-t)^N)$. The scalar cycle-probability series is $D(u)=\sum_jd_j u^j=\exp(\sum_{j\ge k}u^j/j)$ and $b_s=[u^s](1-u)(D(u)-1)$. The known recurrence gives $1/(2k-1)\le d_j\le1/k$ for $j\ge k$. Both $N=n,m$ obey $X=N/k\ge49$, $NS^2\ge147/125$, and $NS\ge147$. The hypotheses imply $k\ge225$ and $-\log C\le1/(49k)$.

For completeness, the block estimates on the numerator coefficients are

$$
b_k=1/k,\qquad
\sum_{k<s\le2k}|b_s|\le(1/2+1/(4k))/k,qquad
\max_{jk<s\le(j+1)k}|b_s|\le1/(2j!k^2)\quad(j\ge2).
$$

For the second block use $sb_s=d_{s-k}-d_{s-1}$ and $d_j\in[1/(2k-1),1/k]$ when $j\ge k$. This gives the initial $1/(4k^2)$ bound. The recurrence then divides the following block maximum by at least $j$. The first block telescopes to its variation plus the single jump at $2k$. For $c=13/25+1/49$, these bounds and Cauchy–Schwarz give

$$
\sum_s|b_s|e^{cs/k}<6/k,\quad
\sum_s s|b_s|e^{cs/k}<15,\quad
\sum_s \sqrt{s}|b_s|e^{cs/k}<10/\sqrt{k}.
$$

Also $\sum_{s>16k}|b_s|<10^{-12}/k$ by summing the factorial block bounds. All these numerical comparisons are checked rationally.

Write $\omega=e^{13/(25k)}$. We use the exact identity

$$
F_N=\sum_a[u^N](D(z_a u)-1)Q_a(u),\qquad
Q_a=\prod_{q\ne a}(1+A_{a,q}),\qquad
A_{a,q}(u)=\sum_{s\ge k}\frac{b_s z_q^{s-1}u^s}{i(q-a)S}.
$$

The following bounds are for coefficientwise majorant series **independent of $a$**. Define

$$
D_+(u)=\sum_s |b_s|u^s/S,\qquad
J_+(u)=\sum_s\frac{|b_s|C^{-s}}{N}
     \left(s-1+\frac{\sqrt{s-1}+1}{S^2}\right)u^s.
$$

The respective coefficient majorants of $A_{a,q}$ and $A_{a,q}'/N$ are $D_+/|q-a|$ and $J_+/|q-a|$, where prime denotes angular derivative. The signed sum over $q$ has coefficient majorant $(\pi/2)\sum_s|b_s|C^{1-s}u^s/S$, with normalized derivative majorant $(\pi/2)J_+$. The [signed kernel argument](../uniform-hilbert/README.md) bounds the sum $\sum_{q\ne a} f_q/(q-a)$ by $\pi/2$ times the variation of any Fourier measure representing $f_q$. Write $z_q^h$ as the Gamma($h$, unit scale) transform at $qS/C$ times $C^{-h}$. The derivative is $h(z_q^{h+1}-Cz_q^h)/S$. The two Gamma densities in the difference reduce to the shape-$h$ density times $x/h-C^2$, with prefactor $C^{-h-1}$. Its variation is at most $C^{-h-1}(1/\sqrt h+S^2)$ from the variance of the Gamma density. For $h=s-1$ the derivative bound follows, with differentiation of $1/S$ contributing the final $+1$ in $J_+$. An individual term uses the same measure bound without the signed sum.

At each distinguished pole $a$ keep the two factors $q=a\pm2$ outside the logarithm. For all far factors in this product, use their log series. For the linear far sum take the full signed bound and add the absolute bound for the omitted two terms. At $u=\omega$ this costs at most $(\pi/2+1)D_{\mathrm{max}}$ with $D_{\mathrm{max}}=2$, because $D_+(\omega)\le6/A\le2$ and the signed numerator moment obeys the same bound before its factor $\pi/2$. The higher log terms cost at most

$$
\frac{D_{\mathrm{max}}^2}{4(1-D_{\mathrm{max}}/4)}\sum_{j\ge2}j^{-2}\le2.
$$

Indeed for $|q-a|=2j\ge4$ each norm is at most $D_{\mathrm{max}}/(2j)$. The geometric logarithm bound uses $1/h\le1/2$ for $h\ge2$. Thus the coefficientwise majorant formed by multiplying the two near factors by the exponential of the far logarithmic envelope has weighted sum at most $4e^{\pi+4}<6000$.

For the derivative of the far logarithm, its linear part costs at most $(\pi/2+1)J_+(\omega)$. The higher parts cost at most $D_{\mathrm{max}}J_+(\omega)/(2(1-D_{\mathrm{max}}/4))\le2J_+(\omega)$. The derivative of the two polynomial factors adds at most one more factor $J_+(\omega)$ times the undifferentiated majorant. These estimates give an $a$-independent coefficientwise majorant for $Q_a'/N$ with weighted sum at most

$$
6000(\pi/2+4)J_+(\omega)<21000,
\qquad
J_+(\omega)\le 15/N+10/(\sqrt k\,NS^2)+6/(kNS^2).
$$

The majorants follow by multiplying series with nonnegative coefficients. In particular the weighted sums also bound all coefficient partial sums. The angular derivatives are justified coefficientwise by local absolute convergence at each positive angle.

## Differentiating the residue approximation

For the approximation to $F_N$ retain the fixed near set $a=\pm1,\pm3,\pm5$ and put $M_a=d_\infty Q_a(z_a^{-1})$, with $d_\infty=e^{-\sum_{j=1}^{k-1}1/j}$. These are the same multipliers for $N=n,m$. At these poles $\rho_a^{-1}\le e^{12/(25k)}$, so $\omega\rho_a\ge e^{1/(25k)}$. All differentiations of the approximate sum use this fixed set.

At a near pole, a product coefficient of degree $T$ leaves $r=N-T$ for the distinguished factor. Define its actual scalar coefficient as zero for $r<k$. In the approximation it is replaced by $d_\infty$ for all $T$. For $r\ge16k$ the error in this replacement is below $10^{-12}/k$ by the tail estimate for $b_s$. Both the value and normalized derivative errors then use the same weighted coefficient bounds, multiplied by $\sum_{a\mathrm{\ near}}\rho_a^N\le6$ or $\sum_{a\mathrm{\ near}}|a|\rho_a^N\le18$. The distinguished derivative also has its degree fraction $r/N\le1$.

When $T>N-16k$, write $T=N-16k+v$, with $v\ge0$. The scalar coefficient difference is at most $1/k$, and

$$
\rho_a^{N-T}\omega^{-T}
\le \rho_a^{16k}\exp(-(13/25)(X-16))e^{-v/(25k)}.
$$

The first exponential is below $1/20{,}000{,}000$ even at $X=49$. For the differentiated distinguished power, the extra absolute factor $|r|/N$ satisfies $(|r|/N)e^{-v/(25k)}\le16/X+25/(eX)<53/100$. This works also for negative $r$ in the full residue series. The $Q_a'/N$ term instead uses the derivative coefficient norm with no extra degree factor.

For far poles $|a|\ge7$, keep their actual coefficient contributions. At the fixed angle divide them into those with $\rho_a^{-1}\le\omega$ and those with $\rho_a^{-1}>\omega$. This split estimates the already differentiated identity, so no indicator is differentiated. In the first group, $\rho_a^r\omega^{-(N-r)}\le\rho_a^N$ for every $k\le r\le N$. The far single-pole first moment $\sum_{|a|\ge7}|a|\rho_a^N$ is below $10^{-8}$. Indeed $\rho_a^N\le[1+(147/125)(a^2-1)/192]^{-96}$, and the checker bounds its first term and the weighted monotone integral from seven. The same moment bounds the mass and the distinguished derivative since $r/N\le1$.

In the second group, $\rho_a\omega<1$, and the largest degree-weighted factor occurs at $r=k$. Thus

$$
\rho_a^r\omega^{-(N-r)}\le\rho_a^k e^{-(13/25)(X-1)}.
$$

Use the pole mass bounds $(9/2)\sqrt X$ and $(33/4)X$ for $\rho_a^k$ and $|a|\rho_a^k$, respectively. The products of these with the exponential decrease for $X\ge49$. At $X=49$ the exponential is below $1/25{,}000{,}000{,}000$. The uniform coefficient majorants allow the pole and coefficient sums to be interchanged in all these estimates.

Writing $\mathcal E_N=F_N-\sum_{a\mathrm{\ near}}M_a z_a^N$, the four parts give

$$
k|\mathcal E_N|<2/1000,qquad
k|\mathcal E'_N|/N<1/100.
$$

## Old-root derivative sign and lag

Put $s=r_0 C$ and $w_a=s+ia\pi$. The [coefficient identity](../fixed-threshold.md) expresses $\sum_N F_Nu^N$ as $(1-t)T_s(r_0u)/(1+e^{r_0u-s})$. Its residue at $u=z_a^{-1}$ is $-(1-t)T_s(w_a)/r_0$. In the pole product $\prod_qD(z_qu)$, the same residue is $-d_\infty Q_a(z_a^{-1})/z_a$ because $D(u)=e^{-\sum_{j=1}^{k-1}u^j/j}/(1-u)$, and $1+A_{a,q}(z_a^{-1})=D(z_q/z_a)$ for $q\ne a$. Both expressions extend meromorphically from zero. The pole product converges locally uniformly away from its poles since $D(z_qu)-1=O(|q|^{-k})$ on compact sets.

The [pole identity for the numerator](../effective-uniform.md#neighboring-residues) gives $(1-t)T_s(w_a)=e^{-H(w_a)}$, where $H(w)=\sum_{b\ge1}e^{-bw}b^{-1}\sum_{j=0}^{k-1}(bw)^j/j!$. Thus $M_a=e^{-H(w_a)}z_a/r_0$ and

$$
\frac{M_a'}{NM_a}=\frac{z_a}{NS}+\frac{\pi H'(w_a)}{NS^2}.
$$

We have $s>15\sqrt k\ge225$. Along each near vertical segment $\log(|w|/s)<51/(100k)$. The gamma-density sum from the [neighboring-residue proof](../effective-uniform.md#neighboring-residues) therefore gives $\pi|H'(w)|\le\pi e^{51/100}(1/s+1/\sqrt{2\pi(k-1)})<17/100$. In particular the normalized multiplier derivative is below $16/100$.

On the real axis, $H(s)\le1+\log(1+3k/(2s))+1/100$. Sum the harmonic terms for $b\le3k/(2s)$ and use the Poisson lower-tail bound $e^{-bs/18}$ for the rest. Combining with the vertical integral bound gives

$$
k|M_1|> e^{-59/50}\frac{A}{\pi+(3/2)A/C}
\ge e^{-59/50}\frac{3}{\pi+(9/2)/C}>23/200.
$$

The nonprincipal near terms divided by the principal pair amplitude have total value below $21/1000$ and total normalized derivative below $7/100$. For $a=3,5$ use $|M_a/M_1|\le e^{(17/100)(a+1)}$, $\rho_3^N<e^{-23/5}$ and $\rho_5^N<e^{-14}$, with derivative cost $a+16/100$. The negative poles are the conjugates.

After dividing by $2|M_1|$, the old value error is below $3/100$. At an old zero its principal sine is above $99/100$ in absolute value. The phase differs from $n\theta$ by less than $19/100$, since $|\Im H(w_1)|<17/100$ and $\theta<1/50$. This proves the alternating sample signs and also fixes the sign of the sine to be $(-1)^j$ within the integer gap of index $j$ at any old zero there. The leading angular derivative has the opposite sign from that sine, and the bound

$$
\frac{|F'_n|}{2n|M_1|}>99/100-16/100-7/100-(1/100)/(23/100)>71/100
$$

shows the other terms preserve it. For the lag, $|F_m|/(2|M_1|)<1+3/100$, and $|B_k|/(nS)\le(2/x+2/\sqrt{x})/A<11/100$ for $x=n/k\ge50$. Hence

$$
\frac{|B_kF_m|}{2nS|M_1|}<12/100.
$$

At an old zero the normalization gives

$$
(n+1)F_{n+1}=SF'_n+B_kF_m.
$$

Indeed multiply the insertion recurrence for $E_{n+1,k}$ by $r_0^{n+1}/(n!(1-t)^{n+1})$. The coefficient multiplying $E_{n,k}$ vanishes, $dt/d\theta=r_0 t/S$, and the cycle pole identity gives $tA_{k-1}=(k-1)!(1-t)^k r_0^{-k} B_k$. Thus at an old zero in gap $j$, the sign of the actual next $F_{n+1}$ is the derivative sign $(-1)^{j+1}$. Reversing the insertion term preserves this sign. Since $t<0$, the corresponding sign for $P_{n+1}$ is $(-1)^j$.

## Global consequence

Use the [independently checked adaptive table](../adaptive-poles/README.md), including its short-cycle circle criterion, its small-threshold result and the complete three-cycle range. For $1{,}408{,}334\le n<4{,}062{,}720$, the adaptive table already covers $4\le x=n/k\le50$ because its largest row cutoff in that range is $1{,}408{,}334$. For $x\ge96$ the circle criterion applies because $0.89\cdot96>47+2.5\cdot15.3$ and $\log n<15.3$.

In the intervening range $50\le x\le96$, use the exterior theorem and the same first middle sample of index $\lfloor7\sqrt n/20\rfloor+1$. It satisfies $nS^2>6/5$, so on the first half of the middle interval $kS\ge\sqrt{(6/5)n}/96>3$. If $A=kS\ge24$, the adaptive middle bounds give the old signs and lag comparison at all such points. For $3<A<24$, we have $kS^2=A^2/k<24^2\cdot96/n<1/25$, and the new comparison applies. The local estimates on both sides of the split give the same integer-sample signs and the true derivative's sign at old roots. The exterior theorem places $H=\lfloor7\sqrt n/20\rfloor$ old roots before sample $H+1$. On the first half of the axis there is one sign change in each consecutive integer sample gap through index $\lfloor n/2\rfloor$. Reciprocity gives the reflected roots and gives the additional root $-1$ when $n$ is odd. The old count is $2(H+\lfloor n/2\rfloor-H-1)+(n\bmod 2)=n-2$, so all these roots are simple, and every gap contains exactly one. The old-root signs of the actual next row alternate, including at the odd central root where the adaptive comparison applies. Its constant and leading coefficients are one, so the two outside intervals and the consecutive old-root gaps exhaust the next degree $n-1$. For $n\ge4{,}062{,}720$ use the previously checked theorem. Thus the stated cutoff covers every threshold.

The smaller finite region remains open outside the available sufficient tests.

Run both checkers with the Python standard library. [Exact checker](check-wide-differentiated-residue.py) · [Replay output](wide-differentiated-residue-output.txt) · [Independent checker](verify-wide-differentiated-residue-independent.py) · [Independent output](wide-differentiated-residue-independent-output.txt)
