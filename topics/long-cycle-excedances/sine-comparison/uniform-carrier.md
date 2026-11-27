# A single principal-residue bound at every middle angle

Use the literal rows and the signed odd pole notation of the [reviewed adjacent sine comparison](README.md). Fix $n\ge10000$, $4\le n/k\le48$, $0<\theta\le\pi/2$, $S=\sin\theta$, $C=\cos\theta$ and $nS^2\ge U=6/5$. The bound is $kD_n/S>322338/10^6$ with no split in $kS$. Its purpose is to eliminate the complex tilt derivative and Poisson-tail estimates from the principal-amplitude input to the original-row formalization.

Write $w_a=C+iaS$, $z_a=1/w_a$ for signed odd $a$, $u_a=w_1/w_a$, and $d_\infty=\exp(-\sum_{j=1}^{k-1}1/j)$. For $|v|<1$ let $D(v)=\exp(\sum_{j\ge k}v^j/j)$. The one-pole factor in $Q_1(w_1)$ equals $D(u_a)$ for $a\ne1$, since $(w_a/(w_a-w_1))(1-u_a)=1$. For $a=-1$ the argument $u_{-1}=e^{2i\theta}$ is on the unit circle and differs from one. Use the continuation $D(v)=\exp(-\sum_{j<k,j\ge1}v^j/j)/(1-v)$ there. The numerator series $B(v)=(1-v)(D(v)-1)$ in the occupied formula is entire, so its evaluation at this boundary point causes no ambiguity. The absolute product argument follows from the summable logarithm bound below. The principal coefficient in the full expansion of the old and successor sizes is the same $M=d_\infty Q_1(w_1)$.

For $|v|\le1$, $v\ne1$, put

$$
L_k(v)=v^k\int_0^1\frac{x^{k-1}}{1-xv}\mathrm{d}x.
$$

On the open disk its power series is $\sum_{j\ge k}v^j/j$. On the punctured unit circle radial continuity gives $D(v)=\exp L_k(v)$. Indeed the straight denominators stay away from zero on any compact radial segment ending at such a $v$. For $0<x\le1$, the real part of $1-v$ is nonnegative, so $|1-xv|=|1-x+x(1-v)|\ge x|1-v|$. Integration gives

$$
|L_k(v)|\le\frac{|v|^k}{(k-1)|1-v|}.
$$

Since $|u_a|=|z_a|$ and $|1-u_a|=|a-1|S|z_a|$,

$$
M=d_\infty\exp Z,\qquad |Z|\le\sum_{a\ne1}|L_k(u_a)|\le
\frac{1}{(k-1)S}\sum_{a\ne1}\frac{|z_a|^{k-1}}{|a-1|}.
$$

Fix a slab $\ell\le n/k\le X$ of the earlier proof, with $K=\lfloor10000/X\rfloor$ and $A_0=\lfloor4\sqrt{12000}/X\rfloor/4\le kS$. The exponent-96 kernel for $k-1$ at $c=(1-1/K)U/(192X)$ bounds the sum in the display. Sum the fixed row $a\ne1$ through absolute odd index 63 and divide the remaining signed mass bound by two. Multiply by $K/((K-1)A_0)$ to get the rational bound $|Z|\le\eta<81/100$ in every slab.

For $|x+iy|\le\eta\le81/100$ one has $e^x\cos y\ge e^{-\eta}$. Put $h=x+\eta\ge0$. Then $y^2\le h(2\eta-h)$ and $(1+h)(2\eta-h)\le(\eta+1/2)^2<2$. Consequently $(1+h)(1-y^2/2)\ge1$ and $e^h\cos y\ge1$ by $e^h\ge1+h$ and $\cos y\ge1-y^2/2>0$. Finally, integrating $1/t$ over $[j-1/2,j+1/2]$ bounds $1/j$ from above, by the midpoint inequality for convex functions. Sum this inequality for $j=2,\ldots,k-1$. It gives $H_{k-1}\le 1+\log((k-1/2)/(3/2))$, hence $2kd_\infty>3/e>12/11$. We therefore use the rational carrier lower bound $(12/11)/\mathrm{ExpUpper}(\eta)$.

Use the principal value and nonprincipal value terms of the [small-angle argument](small-angle.md) in every slab. Its $b>240$ tail estimate is uniform since it only uses $A_0\ge9/4$, $K\ge208$ and $U=6/5$. Use the regular and single-primitive/multiple-primitive exceptional numerator bounds of its large-angle argument with the present $A_0$. Those bounds require only $A\ge A_0$ and $A_0/(AS)\le A_0 X/U$, which holds at every angle in the stated sector. The realized cutoff-jump degree remains $T=n+1-k$. All nine exact scaled margins exceed $322338/10^6$; the smallest is in the slab $44\le n/k\le48$. [Exact checker](check-carrier.py) · [Exact output](carrier-output.txt) · [Independent checker](independent-carrier.py) · [Independent output](independent-carrier-output.txt)

This strengthens the scalar comparison in a sector already covered by the repository’s proof. The independent reviewer checked the integral at the conjugate pole, the all-angle numerator bound, uniform principal truncation, and all nine numerical margins. The full uniform estimate still has no Lean proof. [Independent review](carrier-review.txt) · [Earlier comparison and original statement](README.md)

Run the following from this directory. Both scripts use exact rational arithmetic in the Python standard library. The first uses the rounded bin recurrence and the earlier signed lattice truncated at 63. The independent check uses direct polynomial powers, a different rounding scale and a signed lattice truncated at 67. Each printed margin is a floor in millionths.

~~~sh
python3 -I -B check-carrier.py
python3 -I -B independent-carrier.py
~~~
