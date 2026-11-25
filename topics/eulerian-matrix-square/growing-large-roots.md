# Growing ranks among the largest Eulerian-square zeros

Let $L_n(z)=z^{n-1}H_n(1/z)$ be the reciprocal of the degree-$n-1$ Eulerian-square row after its zero at the origin is removed. There are absolute constants $c,C>0$ such that for every sufficiently large $n$ and every $1\le h\le c\sqrt{n/\log n}$, the $(2h-1)$st and $2h$th largest-modulus zeros of $H_n$ are simple and negative. Every zero of $H_n$ of modulus at least $\exp(C\sqrt{n\log n})$ is simple and negative. This extends the previously fixed-$h$ [cluster theorem](matrix-powers.md). Combined with the [closed-disk theorem](right-half.md) and [compact-annulus result](compact-annuli.md), it leaves intermediate growing moduli for the [transition theorems](eventual.md). The estimates here concern all sufficiently large $n$.

Write $v_h=(h+1)/h$, $s_h=1/v_h$ and
$$
 F_h(u)=1+b_hu+c_hu^2,\quad b_h=h^{-1}+v_h^{-(h-1)},\quad c_h=v_h^{-h}/h .
$$
We use the $p=2$ matrix-power expansion with $A=a+1,B=b+1$. Its exact term is $e_{n,A-1} e_{n-A+1,B-1}z^{A+B-2}$, where $e_{m,k}$ counts permutations with $k$ descents, $A,B\ge1$ and $A+B-2\le n-1$. The modulus of its coefficient is at most $A^n B^{n+1-A}$. For central points $A,B\in\{h,h+1\}$ the relative error in this approximation is $O(n^{-5})$ uniformly. Indeed the explicit Eulerian formula bounds the relative error for $e_{m,b}$ by $(1+e^{-m/(b+1)})^{m+1}-1$. In the central square $m\ge n-h$ and $b+1\le h+1$; the resulting bound decreases faster than every fixed inverse power of $n$. All four central points lie in the feasible range.

At $z=s_h^n u$ put
$$
 K_{n,h}=(h^2 s_h^{2h-2})^n h^{-(h-1)} .
$$
The four central model terms then sum exactly to $K_{n,h}u^{2h-2}F_h(u)$, as follows by evaluating the four pairs $(h,h),(h+1,h),(h,h+1),(h+1,h+1)$. We claim that on the whole complex annulus $1/10\le |u|\le64h$,
$$
 \left|\frac{L_n(s_h^n u)}{K_{n,h}u^{2h-2}}-F_h(u)\right|
 \le C_1 n^{-4}\big(1+b_h|u|+c_h|u|^2\big). \tag{1}
$$

To prove this bound, send each positive integer $A$ to its nearest value $A_0$ in $\{h,h+1\}$ and likewise for $B$. Write $D=|A-A_0|+|B-B_0|$. For $t=1,2,\dots$ the consecutive ratio of $t s_h^t$ is $v_t/v_h$. It equals one at $t=h$ and decreases with $t$. Outside the central pair each step away incurs a factor at most $e^{-\eta_h}$, where
$$
 \eta_h=\log(v_h/v_{h+1})=\log(1+1/(h(h+2)))\ge 1/(h+1)^2 .
$$
This also bounds the loss on the lower side since $\eta_t$ decreases with $t$. The product part $(A B s_h^{A+B-2})^n$ consequently loses at least $e^{-n\eta_h D}$ relative to the corresponding central magnitude.

The remaining factor $B^{1-A}$ costs at most $\exp(3\log(n+1)D)$ in this comparison. At fixed $B$ changing $A_0$ to $A$ costs at most $\exp(\log n\,|A-A_0|)$ since $B\le n$. With $A=A_0$ the only possible gain on changing $B_0$ to $B$ occurs for $B<B_0$. Then $B_0\ge2$ and convexity of $-\log x$ on $[1,B_0]$ gives
$$
 (A_0-1)\log(B_0/B)\le\frac{A_0-1}{B_0-1}(B_0-B)\log B_0
 \le2(B_0-B)\log(n+1).
$$
Finally $|u|^{A+B-A_0-B_0}$ costs at most $\exp(2\log(n+1)D)$ for the displayed annulus and large $n$. Choose the absolute $c$ sufficiently small that $n/(h+1)^2\ge12\log(n+1)$ throughout the range. There are $O(D+1)$ lattice points per fixed central point and distance $D$. Summing the geometric losses for $D\ge1$ and adding the Eulerian approximation errors at the four central points proves (1).

On $|u|=1/10$ the constant coefficient of $F_h$ dominates the two others since $b_h\le2$, $c_h\le1$. On $|u|=64h$ the quadratic term dominates by a fixed factor since $c_h\ge 1/(eh)$, again using $b_h\le2$. Inequality (1) preserves strict dominance at both boundaries. Rouché's theorem therefore counts exactly $2h-2$ zeros of $L_n$ inside the smaller circle and $2h$ inside the larger circle, both after scaling by $s_h^n$.

There are two real roots in between. At $u=-2/b_h$, the quadratic equals $-1+4c_h/b_h^2$, uniformly bounded away from zero on the negative side. In fact $b_h=X+Y$ with $X=1/h$, $Y=v_h^{-(h-1)}$, and $XY/c_h=v_h>1$. Thus $b_h^2/(4c_h)>1$ for every $h$, and this ratio tends to infinity as $h\to\infty$. Also $1\le2/b_h\le2e$ and $1+b_h|u|+c_h|u|^2\le4$ at that point. Inequality (1) gives negative sign there and positive signs at $u=-1/10$ and $-64h$. The two sign changes exhaust the count, giving distinct simple negative zeros. Between adjacent scales the circles are disjoint because $(v_h/v_{h+1})^n\ge(n+1)^{12}>640h$. The counts on the boundaries therefore identify the stated modulus ranks among all complex roots.

For $h=\lfloor c\sqrt{n/\log n}\rfloor$, the outer radius in the reciprocal variable is $64h s_h^n$, and $n\log v_h\le n/h=O(\sqrt{n\log n})$. Thus for a sufficiently large absolute $C$ all original roots with modulus at least $\exp(C\sqrt{n\log n})$ are accounted for by these pairs.
