# The first transition that admits three cycles

Write $P_j(t)=E_{j,k}(t)/t$ for the excedance polynomial with its common zero removed. For every $k\ge3$, the polynomials $P_{3k-1}$ and $P_{3k}$ have simple negative roots and strictly interlace. At every old root the magnitude of the distinguished insertion term is smaller than that of the derivative contribution $x(1-x)P_n'(x)$. Both insertion signs therefore give strict interlacing with the old row.

Set $n=3k-1$, $m=2k$, $M=n-1$, and use the references in the [companion pole proof](three-cycle-poles.md). The old row has at most two cycles. The residual row now has two cycle-count contributions. Its exact pole expression is

$$
F_m=\frac{B_{2k}}{2k}+\frac{B_k^2}{2k^2}.
$$

## Middle angles for $k\ge65$

For $n\sin^2\theta\ge6/5$ use the two-cycle value and derivative comparators from the [two-cycle theorem][two]. Its parameter mesh uses the interval $q=1/3\le k/n\le17/48$. The short fractions of all old two-cycle terms lie in $[1/3,1/2]$, covered by this mesh and its successors, so the value and derivative errors $T+WA$, $U+WB$ hold with exactly the functions there. Here $W=\sum_{j=k}^{2k-1}1/j$. The convexity of $x\mapsto1/x$ gives $1/j\le\int_{j-1/2}^{j+1/2}dx/x$. Thus

$$
W\le\log\left(\frac{2k-1/2}{k-1/2}\right)
\le\log2+\frac1{4k-2}<\frac7{10}.
$$

After division by $2S$, where $S=\sin\theta$, the absolute old-root insertion lag is bounded by the original single-cycle lag bound plus the contribution of $B_k^2/(2k^2)$ in $F_m$. The latter is at most

$$
\frac{|B_k|^3}{4k^2S}\le
\frac{(2(1+T(1/3)))^3}{4\cdot65\cdot5}.
$$

Indeed $|B_k|\le2(1+T(1/3))$, $k\ge65$, and $kS\ge\sqrt{n(6/5)}/3>5$. Write $J$ for the sum of the prior single-cycle bound (at the mesh index $16$) and this increment. The exact rational checker gives

$$
(T+WA)^2+(U+WB+J)^2<(1+W)^2
$$

at $W=0,7/10$. The difference of the left side and right side is convex in $W$ since $A\ge1$. The bound holds throughout the intervening interval. As in the existing two-cycle proof it gives the integer sample signs and the strict derivative comparison at every central old root.

## Exterior roots for $k\ge65$

The full old row coefficient and root isolation argument from the [two-cycle front proof][front] applies unchanged to $n=3k-1$. The old row has at most two cycles and satisfies $n\ge194$ and $k\ge n/3$, as needed for the coefficient bounds and root isolation. In particular it isolates the first $H=\lfloor(7/20)\sqrt M\rfloor$ simple negative roots, places them outside the central sample gaps, and obtains the same derivative lower bound.

For the residual row, the coefficient upper bound in that proof gives, for $1\le p\le2k-1$,

$$
\frac{[t^p]E_{2k,k}}{p^{2k-1}}
\le1+\sum_{j=1}^{p-1}\frac1j
\mathbb P\lbrace \mathrm{Bin}(2k,j/p)=k\rbrace
\le1+\frac{1+\log(2k-1)}{\sqrt{\pi k}}<1.414.
$$

The coefficient vanishes for $p\ge2k$. The binomial point mass is maximal at parameter $1/2$. At that parameter, the central mass is at most $1/\sqrt{\pi k}$, by integrating $\cos^{2k}u\le e^{-ku^2}$ over $[-\pi/2,\pi/2]$ and using the usual integral identity for the central binomial coefficient. The final fraction decreases for $k\ge65$ by differentiation and is below $0.414$ there, using $\log130<4.9$ and $\pi>3.14$.

In the existing convolution argument for the lag, bound the residual coefficient by this factor times its word upper bound. The Stirling prefactor $7/8$ still applies because $a=(k-1)/(3k-2)\in[0.33,1/3]$ implies $a(1-a)\ge0.33\cdot0.67$, and $M\ge191$. The remaining Gaussian lattice sum, derivative lower bound, and geometric tails are unchanged. The old-root ratio bound is therefore

$$
\left|\frac{L(x)}{x(1-x)P_n'(x)}\right|
<\frac{1.414\cdot 777}{80\sqrt M}<1.
$$

At the first middle sample $n\sin^2\theta>6/5$ by the existing join inequality for $n\ge192$. Reflection, sample signs and degree exhaustion give all old roots, just as in the two-cycle theorem. The two next pencils both have leading and constant coefficients one, so the alternating signs at the old roots give every next root.

## Exact finite check

For $3\le k\le64$, the checker independently reconstructs the old and new polynomials by distinguishing the cycle containing label one. In the three-cycle contribution at new size $3k$, all lengths equal $k$. It then checks the insertion identity exactly. Dyadic brackets for the old row are obtained by sign transfer starting from the exact Eulerian row. For each boundary pair both next pencils have certified endpoint signs at every refined old bracket. Reflection and degree exhaustion give the claimed strict alternation at 6,045 old roots in 62 pairs.

From this directory run the checker with Python and python-flint 0.9.0. The path argument locates the existing two-cycle checker helpers.

~~~sh
python3 -IB check-first-three-cycle-boundary.py .
~~~

**Formal verification**　⬜ None. An independent reviewer checked the analytic comparisons and reconstructed the finite certificates. [Independent review](review-first-three-cycle-boundary.md) · [Checker](check-first-three-cycle-boundary.py) · [Replay output](first-three-cycle-boundary-output.txt)

[two]: two-cycle-band.md
[front]: two-cycle-front.md
