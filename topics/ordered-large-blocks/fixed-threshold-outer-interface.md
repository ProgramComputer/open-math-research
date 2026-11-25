# Joining the large-parameter pole expansion to the outer zeros

This research note treats a fixed block threshold $j\ge2$. Set $n=jm+s$, $0\le s<j$, $a=\pi/j$, $\alpha=1+1/(j+1)$, and $L_m=j!(\alpha m)^j$. Write $H_s(x)=\sum_{h\ge0}x^h/(jh+s)!$ for the exponential sections that occur in the [outer limit](fixed-threshold-outer-zeros.md).

The two results below give an exact root index at a moving cut and a uniform principal-pole estimate up to that cut. A condition in the finite middle region would then suffice for eventual real-rootedness and consecutive interlacing at the given threshold.

## An exact index for the exponential sections

For a positive integer $K$ put $X=X_{s,K}=(K+s/j)\pi/\sin a$. For every sufficiently large $K$, the disk $|x|<X^j$ contains exactly $K$ zeros of $H_s$ counted with multiplicity, and its boundary contains none. All sufficiently large $K$ work simultaneously for the finitely many residues $s$.

Indeed, put $Y_s(w)=w^s H_s(w^j)$. Filtering the exponential series gives
$$
Y_s(w)=\frac1j\sum_{\ell=0}^{j-1}\exp(-2\pi\mathrm{i}\ell s/j)\exp(w e^{2\pi\mathrm{i}\ell/j}).
$$
On the arc $w=Xe^{\mathrm{i}\theta}$ with $0\le\theta\le a$, the term with $\ell=0$ has the largest modulus. The term with $\ell=j-1$ can tie it at $\theta=a$. After factoring out $e^w/j$, this term has ratio
$$
V=\exp(2\mathrm{i}sa-2\mathrm{i}X\sin(a)e^{-\mathrm{i}\delta}),\qquad \delta=a-\theta.
$$
Its modulus is $e^{-2X\sin(a)\sin\delta}$ and its phase modulo $2\pi$ is $2X\sin(a)(1-\cos\delta)$, since $X\sin a=K\pi+sa$. Every other ratio is $O(e^{-cX})$ uniformly on the arc, where $c>0$ depends only on $j$. Indeed none of their exponential directions has the same cosine as the principal direction anywhere on the compact arc. At $j=2$ this last sum is empty.

Choose a fixed $A>0$ large enough that $e^{-4 A\sin(a)/\pi}<1/4$. For $\delta\ge A/X$, the bound $\sin\delta\ge2\delta/\pi$ gives $|V|<1/4$. For $0\le\delta\le A/X$, its phase has magnitude at most $A^2\sin(a)/X$, so $\Re V\ge0$ for all large $X$. Thus the factor $jY_s(w)e^{-w}=1+V+O(e^{-cX})$ stays in the open right half-plane. It is real at $\theta=0$ by the real Taylor coefficients, and at $\theta=a$ because $Y_s(Xe^{\mathrm{i}a})=e^{\mathrm{i}sa}X^s H_s(-X^j)$ and $e^w$ has phase $K\pi+sa$. It is therefore positive at both endpoints. Conjugation extends the result to $-a\le\theta\le a$. The net argument change of $Y_s$ along this sector is exactly $2X\sin a$. The identity $Y_s(we^{2\mathrm{i}a})=e^{2\mathrm{i}sa}Y_s(w)$ gives the same change on every sector. The argument principle now counts $jK+s$ zeros of $Y_s$ in the circle. There are $s$ zeros at the origin, and every zero of $H_s$ yields $j$ nonzero preimages. This proves the claim.

## The poles at large negative arguments

For $q>0$ put $v=(1+q)^{-1}$, $p=(j!v)^{1/j}$, $T_j(z)=\sum_{h\ge j}z^h/h!$, and
$$
D_v(z)=T_j(z)+v(2-e^z),\qquad O_{n,j}(-q)/n!=[z^n]((1+q)D_v(z))^{-1}.
$$
Fix a small circle $|z|=R$ on or inside which $T_j$ has no zero except the zero of order $j$ at the origin. For small $p$ there are exactly $j$ zeros of $D_v$ inside, by Rouché's theorem. On setting $z=pZ$, the equation $j!p^{-j}D_v(pZ)=0$ becomes
$$
Z^j+1+p\left(\frac{Z^{j+1}}{j+1}-Z\right)+O(p^2)=0.
$$
The implicit function theorem at the $j$ roots $\omega_\ell=e^{(2\ell+1)\mathrm{i}a}$ of $Z^j+1$ gives analytic branches at $p=0$ with
$$
z_\ell(p)=p\omega_\ell-\frac{\alpha}{j}p^2\omega_\ell^2+O(p^3),\qquad
D_v'(z_\ell)=p^{j-1}\left(\frac{\omega_\ell^{j-1}}{(j-1)!}+O(p)\right).
$$
The principal conjugate pair is $z_0,z_{j-1}$. All other small roots have strictly larger modulus for sufficiently small positive $p$. Indeed $\log(|z_\ell|/p)=-(\alpha/j)p\Re\omega_\ell+O(p^2)$, and $\Re\omega_\ell<\cos a$ for every other index. The principal pair is also closer to the origin than all poles outside $R$.

Write $z_0=r e^{\mathrm{i}\varphi}$, $\beta=\arg D_v'(z_0)$ with the branch tending to $(j-1)a$, and $\Phi_n=(n+1)\varphi+\beta$. Then
$$
\varphi=a-(\alpha/j)p\sin a+O(p^2),
\qquad \beta=(j-1)a+O(p).
$$
These are real-analytic expansions in $p$ extending to zero. In particular, after choosing a fixed sufficiently small $p_0>0$, $a/2\le\varphi<a$ and $\partial_p\Phi_n\le-c_0 n$ uniformly for $0<p\le p_0$ and large $n$, for some $c_0>0$.

Enlarge the coefficient contour to $R$. Minus the two principal residues, divided by the positive normalizer $2/((1+q)|D_v'(z_0)|r^{n+1})$, give $-\cos\Phi_n$. The remaining contribution in this normalization satisfies, for constants $C,c>0$ independent of $p,n$ in the stated range,
$$
|E_n(p)|\le C e^{-c n p},\qquad |E_n'(p)|\le C(n+1)e^{-c n p}.
$$
For a nonprincipal small pole, its contribution is a bounded analytic prefactor times $(r/z_\ell)^{n+1}$. The ratios $r/z_\ell$ extend analytically in $p$ across zero after canceling $p$. Their logarithmic derivatives are bounded near zero, and the modulus comparison gives $|r/z_\ell|\le e^{-c_1 p}$. The derivative therefore costs at most a factor $O(n+1)$. For the contour part, after taking out $(1+q)^{-1}$, the integral and its $p$ derivative are both $O(R^{-n})$ because $D_v$ is uniformly bounded away from zero there. Multiplying by $|D_v'(z_0)|r^{n+1}$ and differentiating gives $O((n+1)\sigma^n)$ for some $\sigma<1$, since $r/p$ and $p^{1-j}|D_v'(z_0)|$ are positive real-analytic near zero and $r/R$ can be uniformly bounded away from one. Decrease $c$ to absorb this part.

Choose a fixed $B$ sufficiently large. On $np\ge B$ and $p\le p_0$, the error is smaller than $1/4$. Around each zero phase $(h+1/2)\pi$ take a band of width $\pi/6$ on each side. The normalized function is strictly monotone in each full band and changes sign across it. Indeed the derivative of $-\cos\Phi_n$ has constant sign there and magnitude at least $(\sqrt3/2)c_0 n$, and increasing $B$ makes the error derivative smaller. In the gaps the principal term has modulus at least $1/2$. At an old zero in this range, $|\cos\Phi_n|\le Ce^{-cnp}$. Since the next phase is $\Phi_n+\varphi$, the sign of the next row is the sign of $\sin\Phi_n\sin\varphi$, namely $(-1)^h$ for an old root in phase band $h$. Increasing $B$ once more makes the summed errors smaller than this sine term, using $\sin\varphi\ge\sin(a/2)>0$.

## The moving cut and consecutive order

Choose one fixed $K$ sufficiently large for the section count and such that $jX_{s,K}/\alpha>2B$ for every $s$. At the reference $q=L_m/X_{s,K}^j$, $p=X_{s,K}/(\alpha m)+O(m^{-j-1})$. Consequently
$$
\Phi_n(q)=(m+1+s/j)\pi-X_{s,K}\sin a+O(m^{-1})=(m+1-K)\pi+O(m^{-1}).
$$
The derivative bound in $p$ gives a unique nearby cut $q_n^\circ$ with phase exactly $(m+1-K)\pi$. The $p$ coordinate moves by $O(m^{-2})$, so $L_m/q_n^\circ\to X_{s,K}^j$. This cut lies strictly inside $np\ge B$ for large $n$. Both the cut and all preceding parameters with $p\le p_0$ are covered by the pole estimate.

The reversed and scaled row converges locally uniformly to $s!H_s$ by the [outer-edge theorem](fixed-threshold-outer-zeros.md). Apply the argument principle count to $H_s$ and Rouché's theorem on a fixed annulus about the limiting radius $X_{s,K}^j$. The original row has exactly $K$ zeros of modulus greater than $q_n^\circ$, including multiplicities, with none on the circle of radius $q_n^\circ$. The outer-edge theorem also gives their reality, simplicity, and strict consecutive alternation.

Here is a sufficient middle-region condition to complete the argument at a fixed $j$. Suppose the principal poles from the [inner-edge theorem](fixed-threshold-inner-zeros.md) continue for all $q>q_*$ as simple nonreal conjugates and are the only poles of minimum modulus. Suppose the continuous argument of their derivative, started at $\pi/2$ at the fold, tends to $(j-1)a$ at infinity. This latter condition follows, for example, if the upper principal pole stays in $0<\arg z<\pi/(j-1)$, since at a pole $D_v'(z)=z^{j-1}/(j-1)!-2v$ then has positive imaginary part.

On a compact interval between the two regions already proved, local contour bounds with a finite cover give an exponentially small relative remainder. The sine of the upper pole angle has positive lower bound on this compact interval, so consecutive signs at old roots hold there too. At the lower edge the relative error is $O(\varphi\sigma^n)$ and the phase starts at $\pi/2$. It follows that for all large $n$ the normalized row has the signs of $-\cos\Phi_n$ at every integer phase point between $q_*$ and $q_n^\circ$. For each $h=1,\ldots,m-K$, take the first hit of $(h+1)\pi$ and the last preceding hit of $h\pi$. These give ordered disjoint sign brackets whose phases lie in $(h\pi,(h+1)\pi)$. This construction uses only continuity. The $m-K$ roots in the brackets and the $K$ exterior roots exhaust the degree, so every root is real and simple. The normalized next-row value at old root $h$ in each such bracket has sign $(-1)^h$ by the consecutive signs in the three regions.

For the $K$ exterior roots use the outer alternation for the first $K+1$ ranks. In increasing modulus, old root $h$ has exterior rank $i=m-h+1$. If the next degree stays $m$, exterior alternation puts the old root between next ranks $i$ and $i-1$, omitting $i-1=0$. If the degree rises to $m+1$, it puts the old root between next ranks $i+1$ and $i$. Both orders amount to the next $h$th root preceding the old $h$th root, which precedes the next $(h+1)$st root whenever that exists. In particular the sign at each of the old exterior roots is also $(-1)^h$. The positive value at $q=0$, these signs at all old roots, and the sign at infinity when the degree increases force strict consecutive alternation. Thus it suffices to check the stated middle-region pole dominance and argument continuation conditions.
