# A derivative-free determinant bound for the small-angle middle

Fix an old size $n\ge10{,}000$, $4\le x=n/k\le48$, and an angle with $0<\theta\le\pi/2$, $nS^2\ge U=6/5$, and $A=kS\le10$, where $S=\sin\theta$ and $C=\cos\theta$. The literal normalized rows are

$$
F_m=\frac{(\pi/S)^m E_{m,k}(-e^{-\pi\cot\theta})}{m!(1+e^{-\pi\cot\theta})^m}.
$$

The normalization is positive. The determinant $\mathcal D_n=\sin((n+1)\theta)F_n-\sin(n\theta)F_{n+1}$ is strictly positive in this sector, by the bounds below. At the integer sample $\theta=j\pi/n$ this gives $(-1)^j F_n>0$. At an old zero in $j\pi<n\theta<(j+1)\pi$ it gives $(-1)^{j+1}F_{n+1}>0$. The determinant controls the actual successor directly. Its proof uses the reviewed pole identities and coefficient envelopes, with no angular differentiation, marked product, or insertion-lag estimate. [Paired-residue inputs](https://github.com/ProgramComputer/open-math-research/blob/ea3e4629db1a664832450fb15b334a0e80da8028/topics/long-cycle-excedances/paired-residues/README.md) · [Degree-block inputs](https://github.com/ProgramComputer/open-math-research/blob/ea3e4629db1a664832450fb15b334a0e80da8028/topics/long-cycle-excedances/degree-blocks/README.md)

## Literal deflation and pole cancellation

Use signed odd indices $a$, $w_a=C+iaS$, and $z_a=w_a^{-1}$. Put $z=z_1=e^{-i\theta}$ and $P(u)=1-2Cu+u^2$. If $H(u)=P(u)\sum_{m\ge0}F_m u^m=\sum_j h_j u^j$, the recurrence for $h_j$ and the sine addition formula telescope to

$$
\mathcal D_n=\sum_{j\le n+1}h_j\sin((1-j)\theta).
$$

The literal generating function is $(1-t)T_s(r_0u)/(1+e^{r_0u-s})$ with $s=\pi\cot\theta$, $r_0=\pi/S$, and $T_s$ the exponential of a finite polynomial. Thus $H$ removes exactly the two principal poles and has its next actual poles at $|w_3|=\sqrt{1+8S^2}$. Write the principal contributions to the coefficients as $M z^m+\overline{M z^m}$. At $u=z$ the eliminated pole belonged to the conjugate multiplier. Hence $z^{-1}H(z)=2iS\overline M$ and the full imaginary sum is $2S\Re M$. The difference from $\mathcal D_n$ is the imaginary Taylor tail from degree $n+2$. For a single nonprincipal residue summand $M_a/(1-z_a u)$, its part of that complex deflated tail, multiplied by $z^{-1}$, is exactly

$$
M_a (w_a-w_1)(z_a z)^{n+1}.
$$

The geometric denominator $1-z_a z=z_a(w_a-w_{-1})$ cancels one deflating factor. The resulting bound is $S|a-1||M_a||z_a|^{n+1}$. This calculation applies to a single meromorphic summand or a finite chosen residue set. The proof below uses the actual occupied expansion for the full row. [Literal generating function](https://github.com/ProgramComputer/open-math-research/blob/ea3e4629db1a664832450fb15b334a0e80da8028/topics/long-cycle-excedances/fixed-threshold.md#poles-and-the-two-adjacent-coefficients)

## A derivative-free occupied term bound

Let $q_{a,T}=[u^T]Q_a(u)$, with the actual $Q_a$ in the cited occupied-pole identity. Put $\widetilde d_r=d_r$ if $r\ge k$ and zero otherwise, for all integer $r$. The numerator coefficient $b_s=[u^s]\bigl(1-u\bigr)(D(u)-1)$ is $\widetilde d_s-\widetilde d_{s-1}$, with zero extension to negative $s$. For a fixed $T$ put $r=n-T$. The contribution to $\mathcal D_n$ from this pole and degree is exactly

$$
z_a^r q_{a,T}\left(\widetilde d_r[\sin((n+1)\theta)-z_a\sin(n\theta)]
-b_{r+1}z_a\sin(n\theta)\right).
$$

For any real $v$, multiplication by $w_a$ gives the exact identity

$$
\sin(v+\theta)-z_a\sin v=S z_a\bigl(\cos(v+\theta)+ia\sin(v+\theta)\bigr).
$$

Its modulus is at most $S|a||z_a|$, since $|a|\ge1$. Thus, after scaling the determinant by $k/S$, the nonprincipal value cost is bounded termwise by $k|\widetilde d_r||a||z_a|^{r+1}|q_{a,T}|$. The separate numerator cost on all poles is bounded by $(k/S)|b_{r+1}||z_a|^{r+1}|q_{a,T}|$. The first is zero unless $r\ge k$, and the second is zero unless $r+1\ge k$.

At the principal pair put $A_n=\sum_T(\widetilde d_{n-T}-d_\infty)z^{-T}q_{1,T}$. Then the old and new errors from this pair are $2\Re(z^n A_n)$ and $2\Re(z^{n+1}A_{n+1})$. The determinant of those errors equals

$$
2S\Re A_n-2\sin(n\theta)\Re\bigl(z^{n+1}(A_{n+1}-A_n)\bigr),\qquad
A_{n+1}-A_n=\sum_T b_{n+1-T}z^{-T}q_{1,T}.
$$

Thus the separate all-pole numerator cost already covers the principal difference. The remaining principal cost after scaling is $2k|A_n|$. The principal amplitude in the reviewed small-angle bound gives $2k\Re M>(47/100)(97/100)$, the target for the sum of the errors. The principal subtracted series converges absolutely under the reviewed weighted product bounds. The nonprincipal occupied terms involve only finitely many degrees, with absolute convergence in their pole indices.

## Exact bin arithmetic

Use the original width-four bins. A bin $b$ for primitive total degree $T$ has $T/k\le h=b/4$ and $T/k\ge g=\max(1,b/5)$ for $b>0$, with $g=h=0$ for $b=0$. On each aspect slab $\ell\le x\le X$, put

$$
 y=\max(1/X,1-h/\ell),\qquad c=yU/192.
$$

Let $Q_b$ be the reviewed unmarked product majorant, including $Q_0=1$. For $r\ge k$, or for $s=r+1\ge k$ in the numerator term, the corresponding degree divided by $n$ is at least $y$. Since $k\ge209$, the upper bound $(1+c(a^2-1))^{-96}$ for $|z_a|^{r+1}$ follows from the reviewed Bernoulli estimate, or from the pointwise 96th-power theorem in the previous scratch package. This requires no half-power kernel.

- The principal value cost is at most $2\sum_{b\le240}e(\ell-h)Q_b+10^{-4}$ using the existing $e$ bounds and the unmarked part of the reviewed tail estimate.
- The nonprincipal value cost uses the first moment of the 96th-power kernel over $|a|\ge3$, multiplied by $Q_b$ and by $4/7$ if $\ell-h\ge2$, or one otherwise. The bin can occur only if $g+1\le X$ and $b\le5X$.
- For $s=r+1>k$, write $g_s=\max(1,\ell-h)$. The existing numerator difference bounds give $k^2|b_s|\le1$ when $g_s\le2$. If $g_s>2$, use $1/(2(\lceil g_s\rceil-1)!)$. The left endpoint may itself be an integer, so the previous factorial block is retained there. Multiply by the all-pole mass of the same kernel and by $Q_b/A_0$, where $A\ge A_0$ is the reviewed rational lower bound for the slab.
- For $s=k$ the exceptional $b_k=1/k$ gives normalized cost $1/S\le 10X/U$ because $U\le xAS$. This atom can occur only when $b/4\ge T/k=x-1+1/k>\ell-1$. Both numerator cases require $g+1\le X+1/K$ and $b<5X$, where $K=\lfloor10{,}000/X\rfloor$. This retains the upper-size boundary cases where $r=k-1$.

The rational replay imports the reviewed lattice and coefficient routines byte-for-byte at the linked revision. The four printed cost columns are ceilings in millionths, and the margin is the floor of the exact difference from $(47/100)(97/100)$.

| Aspect slab | Principal value | Other value | Regular numerator | Atom | Margin |
| --- | ---: | ---: | ---: | ---: | ---: |
| 10–16 | 643 | 63943 | 263 | 33924 | 357129 |
| 16–22 | 104 | 71088 | 3 | 358 | 384348 |
| 22–28 | 101 | 84319 | 1 | 4 | 371477 |
| 28–34 | 101 | 106820 | 1 | 1 | 348980 |
| 34–40 | 101 | 137495 | 1 | 1 | 318305 |
| 40–44 | 101 | 161380 | 1 | 1 | 294420 |
| 44–48 | 101 | 164099 | 1 | 1 | 291701 |

The aspects below 10 are absent because $nS^2=x^2A^2/n$ gives $x^2\ge120$ in the stated sector.

## Upper-size cycle-count boundary

When $n+1=mk$, the newly possible exact $m$-cycle block contributes only $(B_k/k)^m/m!$ to $F_{n+1}$, where $B_k=\sum_a z_a^k$. This follows directly from the literal exponential formula since that block must use $m$ cycles all of length $k$. Its contribution to the determinant is $-\sin(n\theta)(B_k/k)^m/m!$. It does not vanish identically. The corresponding deflated degrees $n+2$ and $n+3$ sum to $+(B_k/k)^m\sin(n\theta)/m!$ in the imaginary tail, by $2C\sin((n+1)\theta)-\sin((n+2)\theta)=\sin(n\theta)$. Thus those two tail terms cancel the truncated atom in the full carrier exactly. Here $m\ge11$ and $kS^2\ge U/48=1/40$. Bernoulli gives

$$
|B_k|\le\sum_a |z_a|^k\le \sum_a (1+(a^2-1)/80)^{-1}<18.
$$

Indeed the last sum is at most $2+\int_1^\infty80/(t^2+79)\mathrm{d}t<2+40\pi/8<18$ by monotone comparison on the two signed odd tails. Thus the literal newly allowed block contributes less than $10^{-11}/11!$. The broader $b_k$ atom above includes terms with fewer than $m$ cycles and is bounded separately.

## Exact obstruction to the direct absolute Cauchy bound

Take $n=10031$, $k=209$, $S=364/33125$, and $C=33123/33125$, from $\theta=2\arctan(1/182)$. This lies in the stipulated sector and $n+1=48k$. For any permitted circle radius $1<R<|w_3|$, the Cauchy coefficient constant is at least $|H(0)|=1$. Hence the usual geometric absolute tail estimate is at least $1/[R^{n+1}(R-1)]>2000/243$. Here $R-1<4S^2<1/2000$ and $R^{n+1}<\exp(4(n+1)S^2)<e^5<243$. The carrier $2S\Re M$ is below $2S^2<1/4000$, since the reviewed vertical estimate gives $|M|\le(S/\pi)e^{0.18}<S$.

Even retaining the individual absolute sine weights in this coefficientwise Cauchy estimate still fails. Some integer $m\in[n+1,n+300]$ satisfies $|\sin(m\theta)|\ge1/2$. Choose the first peak of the absolute sine beyond $(n+1)\theta$ and round its angular index upwards, using $\pi/\theta+2<300$ and $\theta<1/20$. The coefficient with $j=m+1$ alone costs at least $(1/2)R^{-j}>1/1458$ since $4(n+301)S^2<6$. This is a limitation of that Cauchy estimate, independent of the true tail magnitude.

Run the [exact checker](check-bounds.py) and the [separate obstruction checker](obstruction.py) from this directory. The complementary estimate is in the [large-angle proof](large-angle.md).
