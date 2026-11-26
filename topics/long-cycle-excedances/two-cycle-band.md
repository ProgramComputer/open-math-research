# Interlacing throughout the one- and two-cycle range

Let $E_{n,k}$ be the excedance polynomial for permutations with all cycles of length at least $k$, and let $P_n=E_{n,k}/t$. Here $k$ stays fixed when comparing consecutive rows. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances)

**Partial theorem.** Whenever $k\ge3$ and $k\le n\le3k-2$, the old and new polynomials $P_n,P_{n+1}$ have simple negative roots and strictly interlace. Both signs of the term creating a new $k$-cycle preserve the old derivative’s signs. This includes every consecutive pair for which the new permutation can have at most two cycles.

Write $D(t)=t(1-t)P_n'(t)$ and $L(t)=\binom n{k-1}A_{k-1}(t)E_{n+1-k,k}(t)$, so $P_{n+1}(x)=D(x)+L(x)$ at an old root. For $n<2k-1$ the rows are ordinary Eulerian polynomials and $L=0$. The first nonzero lag at $n=2k-1$ has a separate proof. We consider $2k\le n\le3k-2$. [First transition](first-lag.md)

## A finite formula for the two-cycle polynomial

For $t=-e^{-s}$, $s\ge0$, put $r=(s^2+\pi^2)^{1/2}$, $\theta=\arg(s+i\pi)$, $S=\sin\theta$, and $z_p=(\cos\theta+ipS)^{-1}$ for odd $p$. Let $B_m=\sum_{p\text{ odd}} z_p^m$ and
$$
F_n(\theta)=\frac{r^n E_{n,k}(t)}{n!(1-t)^n}.
$$
The normalized weight of an $m$-cycle is $B_m/m$. Splitting by cycle count therefore gives
$$
f:=\frac n2 F_n=\frac{B_n}{2}+\sum_{j=k}^{n-k} w_j\frac{B_jB_{n-j}}{2},\qquad
w_j=\frac{n}{2j(n-j)}.
$$
The division by two for an unordered pair of cycles is included in $w_j$. Put $W=\sum_j w_j=\sum_{j=k}^{n-k}1/j$. We have $0\le W\le\log2<7/10$ by comparing that sum to the integral from $k-1$ to $n-k\le2k-2$. [Eulerian pole identity, equation (5)](first-lag.md)

## Comparing the value, derivative and lag in the middle

Assume $n\ge192$ and $nS^2\ge6/5$. We prove both that $f$ has sign $(-1)^l$ at the samples $\theta=l\pi/n$ in this range and that $|L(x)|<|D(x)|$ at every old root in it. Set $N=192$, $c=6/5$, $\beta=c/N$, and $K(p)=1+\beta(p^2-1)$. For $m/n\ge a$, with $h=Na/2$, monotonicity of $(1+u/n)^n$ gives
$$
|z_p|^m=(1+(p^2-1)S^2)^{-m/2}\le K(p)^{-h}.
$$
We use values of $a$ on the mesh of denominator 48 with $a\ge1/3$. In particular $h$ is integral. Since $|z'_p|\le |p|\,|z_p|^2$ and $|z_p|\le1$, the error $e_m=B_m/2-\cos(m\theta)$ and its derivative satisfy
$$
|e_m|\le T(a),\qquad |e_m'|\le m U(a).
$$
Here $T(a)$ is the sum of $K(p)^{-h}$ over $p=3,5,7,9$, plus $J/9$. For $U(a)$ sum $pK(p)^{-h}$ at the same indices and add $J=K(9)^{1-h}/(4\beta(h-1))$. Beyond nine, each tail is bounded by half its integral starting at nine, and the unweighted integrand is at most one ninth of the weighted one. The weighted integrand is decreasing there because $(2h-1)\beta p^2>1-\beta$. These convergent majorants justify differentiation.

For $u\le\min(j,n-j)/n\le v$ in one mesh interval define
$$
a_{uv}=1+2(T(u)+T(1-v)+T(u)T(1-v)),
$$
$$
b_{uv}=1-2u+2v\bigl(T(1-v)+U(u)(1+T(1-v))\bigr)
+2(1-u)\bigl(T(u)+U(1-v)(1+T(u))\bigr).
$$
Indeed the two principal cosine factors give $2\cos(j\theta)\cos((n-j)\theta)=\cos(n\theta)+\cos((2j-n)\theta)$. The latter cosine has absolute value at most one and derivative at most $n(1-2u)$. Expanding the terms involving at least one $e_m$ gives the other summands in these bounds by the product rule.

Choose $i\in\{16,\ldots,23\}$ so $q=i/48\le k/n\le q_+=(i+1)/48$. Let $A,B$ be the respective maxima of $a_{uv},b_{uv}$ over the mesh intervals in $[q,1/2]$. Put $T=T(1)$ and $U=U(1)$. We have
$$
|f-(1+W)\cos(n\theta)|\le T+WA,\qquad
|f'/n+(1+W)\sin(n\theta)|\le U+WB.
$$

At an old root, multiplying $D$ and $L$ by $t r^{n+1}/(n!(1-t)^{n+1})$ gives, respectively,
$$
S F_n'(\theta),\qquad B_k B_{n+1-k}/(n+1-k).
$$
For the derivative use $t\,d\theta/dt=\pi/r^2$. The derivative of the normalizing factor multiplies the vanishing old row. For the lag, the residual permutation size $n+1-k$ lies in $[k,2k-1]$ and hence admits only a single cycle. The magnitude of the lag, after dividing this comparison by $2S$, is at most
$$
J_i=\frac{2(1+T(q))(1+T(1-q_+))}{15(1-q_+)},
$$
since $(n+1-k)S\ge(1-q_+)\sqrt{nc}>15(1-q_+)$. In the same units the derivative term has magnitude $|f'|/n$.

For these eight threshold intervals the following fixed rational inequality holds throughout $0\le W\le W_i=\min(7/10,(1-2q+1/N)/q)$:
$$
(T+WA)^2+(U+WB+J_i)^2<(1+W)^2. \tag{1}
$$
The upper bound $W_i$ uses at most $n-2k+1$ terms each at most $1/k$. The difference of the left and right sides of (1) is convex in $W$ because $A\ge1$. At both endpoints of all eight intervals the left side is less than $99(1+W)^2/100$, by rational addition, multiplication and integer powers in the displayed formulas. The following short checker reproduces all 16 comparisons. [Exact rational calculation](verify_two_cycle_bounds.py)

At a sample, (1) forces $|f-(1+W)\cos(n\theta)|<1+W$. At a zero of $f$, it gives $(1+W)|\sin(n\theta)|>U+WB+J_i$ using $\sin^2+\cos^2=1$. Consequently $|f'|/n>J_i$ there, proving the strict lag inequality.

## Covering every old root

Let $H=\lfloor(7/20)\sqrt{n-1}\rfloor$. The small-root argument isolates the first $H$ simple negative roots, gives $|L|<|D|$ there, and shows that they precede the sample $(H+1)\pi/n$ in order of increasing modulus. [Small-root argument](two-cycle-front.md)

At the first sample $n\sin^2\theta>6/5$. Indeed put $b=(7\pi/20)\sqrt{n-1}/n<\theta$, use $b^2<121/(100n)$ and $\sin b\ge b-b^3/6$, and check
$$
\left(\frac7{20}\frac{333}{106}\right)^2\frac{191}{192}
\left(1-\frac{121}{115200}\right)^2>\frac65.
$$
All samples $l=H+1,\ldots,\lfloor n/2\rfloor$ therefore have alternating signs. Reflect to $l=n-\lfloor n/2\rfloor,\ldots,n-H-1$ using $E_{n,k}(1/t)=t^{-n}E_{n,k}(t)$, giving sign $(-1)^l$ there as well. We obtain $n-2H-2$ disjoint gaps between samples. These give $n-2H-2$ distinct negative old roots. The $H$ small and $H$ reciprocal large roots lie strictly outside those gaps. This exhausts the degree $n-2$ of $P_n$. Both old-root insertions preserve the derivative sign in all gaps by the middle estimate and reflection. At the two outer ends both next-row pencils (the original row with either insertion sign) have constant and leading coefficient one. Alternation therefore exhausts the next degree $n-1$ and proves strict interlacing.

For $2k\le n\le3k-2$ with $n<192$ an exact calculation certifies all 3,007 transitions. It reconstructs the polynomials from the cycle containing label one, isolates the old roots with dyadic intervals, and checks both pencils by endpoint signs and degree exhaustion. A second reconstruction from consecutive insertions reproduces all three coefficient vectors for each transition. Combining this finite proof with the analytic ranges establishes the stated theorem. The first transition outside this theorem runs from $3k-1$ to $3k$, when three cycles can first occur. [Finite argument, data and reproduction](two-cycle-finite.md) · [Independent agent-assisted review](review-two-cycle-band.md)

**⬜ None.** The result has a written proof and exact arithmetic checks.
