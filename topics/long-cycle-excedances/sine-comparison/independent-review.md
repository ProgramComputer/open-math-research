# Independent review of the bounded-aspect adjacent sine estimate

The two written estimates and their rational bounds establish

$$
\frac{kD_n}{\sin\theta}>\frac{291701}{10^6},
\qquad
D_n=\sin((n+1)\theta)F_n-\sin(n\theta)F_{n+1},
$$

for integers $n\ge 10000$ and $4\le n/k\le48$, at all angles $0<\theta\le\pi/2$ with $n\sin^2\theta\ge6/5$. Here $F_m$ is the positive angular normalization of the literal excedance enumerator. The large-angle estimate separately gives $kD_n/\sin\theta>473268/10^6$ when $k\sin\theta\ge10$. This was an agent-assisted independent review. I rederived the occupied-pole identity and the boundary estimates and checked both strict rational bounds with an independent implementation. I found no mathematical gap in the stated estimate.

## Literal definition and occupied poles

Alexandersson's conjecture concerns consecutive rows at every size $n\ge k$ for every $k\ge3$. The enumerator $E_{m,k}(t)$ counts permutations of $m$ labels by the number of labels $i$ with $i<\pi(i)$, subject to every cycle having length at least $k$. Order-preserving relabeling preserves excedances within a cycle. Writing the cycle's largest label first gives the Eulerian cycle weight $tA_{j-1}(t)$ for length $j\ge2$. The labeled exponential formula and the Eulerian power sum give the literal normalization

$$
F_m=\frac{(\pi/S)^m}{m!(1-t)^m}E_{m,k}(t),
\qquad
S=\sin\theta,\quad t=-\exp(-\pi\cot\theta).
$$

The logarithm of its generating function has coefficient $\frac{1}{j}\sum_a z_a^j$ in degree $j\ge k$, with $a$ ranging over signed odd integers and $z_a=(\cos\theta+iaS)^{-1}$. This follows from the partial fractions of the logarithmic derivative of the Eulerian generating function, whose simple poles have residue $-1$. The resulting coefficient sum is absolutely convergent. [Alexandersson's statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Literal generating function](https://github.com/ProgramComputer/open-math-research/blob/ea3e4629db1a664832450fb15b334a0e80da8028/topics/long-cycle-excedances/fixed-threshold.md#poles-and-the-two-adjacent-coefficients)

For a finite set of poles, expand the product of $D(z_a u)$ by its occupied subsets, where $D(v)=\exp(\sum_{r\ge k}v^r/r)$. Set $B(v)=(1-v)(D(v)-1)$. Partial fractions on the geometric denominators select a distinguished pole $a$ in each nonempty subset. Each other occupied pole $q$ contributes the multiplier

$$
\frac{1}{1-z_q/z_a}=\frac{z_q^{-1}}{i(q-a)S}.
$$

The distinguished factor is therefore $D(z_a u)-1$, and the other factors in $Q_a(u)$ have the power $z_q^{s-1}$ in degree $s$. Each term contributing to a fixed degree has at most that degree divided by $k$ occupied factors. The sums over the pole indices converge absolutely using the powers $r\ge k$ for the distinguished term and $s-1\ge k-1$ for each primitive factor. The locally uniformly convergent meromorphic product gives the same principal residue as the literal generating function. [Occupied identity](https://github.com/ProgramComputer/open-math-research/blob/ea3e4629db1a664832450fb15b334a0e80da8028/topics/long-cycle-excedances/uniform-hilbert/README.md)

For residual degree $T$ and $r=n-T$, the relation $\widetilde d_{r+1}=\widetilde d_r+b_{r+1}$ includes $r=k-1$, since the distinguished series omits its degree-zero term. Multiplying $\sin(v+\theta)-z_a\sin v$ by $w_a=z_a^{-1}$ gives $S(\cos(v+\theta)+ia\sin(v+\theta))$, whose modulus is at most $S|a|$. Thus the two absolute error weights in the scaled determinant are $k\widetilde d_r|a|\rho_a^{r+1}$ and $(k/S)|b_{r+1}|\rho_a^{r+1}$, with $\rho_a=|z_a|$. Pairing the principal poles in the small-angle regime gives $2S\mathrm{Re}(M_1)$ and, after scaling, the separate old coefficient replacement error $2k|A_n|$. The numerator cost includes the differences from both principal poles. The optional deflation identity also checks by telescoping. The infinite Taylor tail of a single nonprincipal term cancels one geometric denominator. The bound itself uses the occupied expansion directly. [Small-angle argument](small-angle.md)

## Coefficient, lattice, and boundary bounds

The cycle recurrence $r d_r=\sum_{j=0}^{r-k}d_j$ gives $1/(2k-1)\le d_r\le1/k$ for $r\ge k$. The harmonic sum on $[k,2k)$ and the logarithm tangent at $7/4$ give the stronger bounds used for $k\ge100$. For $s>k$, the numerator recurrence is $s b_s=d_{s-k}-d_{s-1}$. The initial jump gives $b_k=1/k$. The first block has telescoping variation in its interior and the following upper-end jump

$$
b_{2k}=\frac{k-1}{2k^2(2k-1)}<\frac{1}{4k^2}.
$$

For $jk<s\le(j+1)k$ with $j\ge2$, the pointwise factorial bound follows by induction, using at most $k-1$ earlier differences and the preceding block maximum. The proof retains the preceding factorial block when the lower bound on $s/k$ is an exact integer. Summing the factorial tail bounds the principal coefficient replacement error. The two coarse cases use $0.547\le kd_\infty\le4/7$. [Cycle and bin bounds](https://github.com/ProgramComputer/open-math-research/blob/ea3e4629db1a664832450fb15b334a0e80da8028/topics/long-cycle-excedances/degree-blocks/README.md)

The least possible $k$ is 209, so the exponent in the 96th-power Bernoulli bound applies to all distinguished and primitive terms, including the primitive power $s-1$. Beyond a positive odd cutoff $P$, the signed odd first-moment tail is at most $(1+c(P^2-1))^{-95}/(190c)$ by monotone integration. Dividing by $P$ bounds the mass tail. The off-diagonal tail has an additional factor at most $1/2$ because the odd-pole gaps are at least two. For the retained lattice it suffices to check distinguished poles up to $|a|=P+2$, since each retained denominator increases farther out. The bin $i=\lceil4s/k\rceil$ bounds each primitive variation with its lattice and angle factors. Exponentiating the nonnegative polynomial $L$ bounds products over distinct occupied poles by allowing repetitions. The residual bounds $g\le T/k\le h$ give $\max(1/X,1-h/\ell)$ as a lower bound for both $r/n$ in the old value and $(r+1)/n$ in the new numerator. The weighted first-block mass is below $0.51$, and the subsequent block masses are at most $0.51/j!$. The weighted exponential bound then verifies the small-angle principal tail below $10^{-4}$. [Principal and weighted tail estimates](https://github.com/ProgramComputer/open-math-research/blob/ea3e4629db1a664832450fb15b334a0e80da8028/topics/long-cycle-excedances/paired-residues/README.md)

The small-angle residue is $M_1=z_1\exp(-H(s+i\pi))/r_0$, with $r_0=\pi/S$ and $s=r_0\cos\theta$. Expanding $\log(1+\exp(w-s))$ around zero and substituting at the pole gives the truncated Poisson expression for $H$. Its derivative on the vertical segment is bounded by a sum of gamma densities of order $k-1$. Their real mesh sum is at most $1/s$ plus the maximum density, by unimodality. Stirling bounds the maximum, and the extra complex modulus factor is at most $\exp(A^2/(2k\cos^2\theta))$, where $A=kS$. On the real axis, the Poisson lower-tail estimate gives $\exp(-bs/50)$ for the terms with $b>5k/(4s)$. Their sum is under $0.01$. The harmonic cutoffs give $2k|M_1|>0.47$ and the bound on the argument gives $\cos(\arg M_1)>0.97$. The large-angle main term is $2kd_n\ge1.094$ from the two principal poles in the constant bin. [Residue identity](https://github.com/ProgramComputer/open-math-research/blob/ea3e4629db1a664832450fb15b334a0e80da8028/topics/long-cycle-excedances/differentiated-residues/README.md) · [Large-angle argument](large-angle.md)

The numerator restriction $g+1\le X+1/K$ allows $r=k-1$. The restriction $b<5X$ follows from $T/k\le X-1+1/k<X$. When $r+1=k$, there is one residual degree $T=n+1-k$, so its upper bin bound must satisfy $b/4\ge T/k>\ell-1$. If $n+1=mk$, the newly possible full $m$-cycle block is $(B_k/k)^m/m!$ in the literal successor row. Its contribution to the determinant is the product of this block and $-\sin(n\theta)$, accounted for by the numerator atom. The deflated Taylor terms of degrees $n+2$ and $n+3$ cancel that contribution in the infinite carrier. It remains present in the literal finite determinant. [Upper-size boundary](small-angle.md#upper-size-cycle-count-boundary)

For the large-angle atom, a single primitive contributes at the one exact degree $T$. The inequality $T/k>\ell-1$ gives its stated factorial bound and $(T-1)/n\ge(\ell-1-1/K)/X$ gives its lattice argument. The outer $1/S$ and the primitive $1/S$ combine with $k^{-2}$ to give $1/A^2\le1/A_0^2$. Products with at least two primitives retain a factor of at most $A_0/A$. The subtraction $Q_b-L_b$ uses the same rounded-up linear coefficient $L_b$ used to compute $Q_b$. Since $Q_b\ge[v^b]\exp L$, the difference bounds $[v^b](\exp L-1-L)$ in positive bins. Finally, $(A_0/A)/S\le A_0X/U$ follows from $xAS=nS^2\ge U=6/5$. The small-angle estimate uses the whole atom bin with $1/S\le10X/U$. Its sector has $x^2\ge120$, so slabs below $x=10$ require only the large-angle estimate. [Large-angle atom](large-angle.md)

## Reproduction

I replayed both original scalar scripts and checked that their imported coefficient and lattice routines match the public files at the cited revision byte for byte. The consolidated checker asserts both strict thresholds. [Rational checker](check-bounds.py) · [Expected output](bounds-output.txt)

The independent checker uses $P=67$, a $2^{-52}$ grid, and direct truncated powers of the nonnegative linear majorant. It accumulates the contribution of products with at least two primitives separately. The least small-angle margin has floor 291701 in millionths on $[44,48]$. The least large-angle margin has floor 473268 in millionths on $[6,10]$. Both comparisons with those rational thresholds are strict. Run both checks from this directory.

~~~sh
python3 -I -B check-bounds.py
python3 -I -B independent-check.py
~~~

[Independent rational checker](independent-check.py)

The Arb replay checked thirty specified $(n,k,S)$ points around five upper-size cycle boundaries and forty-two normalized coefficients from twenty-one small $(n,k)$ pairs against direct permutation enumeration. Using python-flint 0.9.0 reproduced the point JSON byte for byte. Those checks cover the specified values and the small-row normalization identities. Uniformity comes from the written estimates and rational slab bounds. [Point checker](check-sine.py) · [Point results](sine-points.json)

## Interlacing and formal coverage

The exterior witnesses in `original_all_aspect_exterior` precede integer phase sample $L=1+\lfloor7\sqrt n/20\rfloor$, where the angular lower bound already holds. Positivity of the determinant gives the old signs at every subsequent integer phase and the actual successor signs at each old zero between samples. The $\lfloor n/2\rfloor-L$ open lower-half gaps and the exterior witnesses give $\lfloor(n-2)/2\rfloor$ distinct old roots of modulus below one. Reciprocity gives their partners. If $n=2N+1$, the old row vanishes at $-1$ and the determinant gives the literal successor sign $(-1)^{N+1}$ there. For even $n$ the midpoint is an integer sample with a nonzero old value. The count exhausts the old quotient degree $n-2$, proving simplicity. The successor quotient signs, together with its constant and leading coefficients of one, give roots in all old-root gaps and both outer intervals. The count exhausts its degree $n-1$. This yields strict negative interlacing of the quotients and a simple common zero of the literal rows throughout the bounded-aspect range. Alexandersson's all-size statement also includes $n<10000$ and aspects outside $[4,48]$.

The Lean files prove the finite deflation telescope, the principal trigonometric identity, and the sample and old-root signs from determinant positivity. The root-count step uses signed integer windows. I rebuilt the standalone deflation module and the local conditional seam assembly with Lean 4.19.0 (commit 6caaee842e94), using Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. The axiom reports listed `propext`, `Classical.choice`, and `Quot.sound`. The local seam assembly defines its own literal enumerator and takes the exterior witnesses and the passage to complete root lists as hypotheses. I attempted to rebuild `RepositoryPairedSine.lean` with the local driver, which failed at the missing `LongCycleBounds` import. The production theorem `original_interlacing_of_paired_sine` has a hypothesis of uniform determinant positivity. The analytic residue and coefficient estimates, the rational bounds, and the uniform determinant estimate remain outside the Lean proof checked in this review. I did not perform an independent kernel replay.
