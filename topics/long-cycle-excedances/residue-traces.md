# A sum of squares for the noncentral insertion ratios

For a real-rooted old row with simple negative roots, put $\mu(x)=L(x)/D(x)$ as in the [central-root theorem](central-insertion.md). Reciprocity gives $\mu(x)=\mu(1/x)$. Let $S$ be the sum of $\mu(x)^2$ over one representative of each reciprocal orbit, counting $-1$ once when present. If $S<1$, each old root has $|\mu(x)|<1$, so the two insertion pencils $D\pm L$ have the derivative’s sign there. With the outer signs this gives strict interlacing by induction. The central-root theorem also allows its squared term to be omitted in this sufficient condition. An all-size bound for the other terms remains open. [Insertion argument](insertion-lag.md)

For a root-free exact calculation use $y=t/(1+t)^2$. If $m=\deg P_n$, write
$$
P_n(t)=(1+t)^mG(y),\qquad L(t)=(1+t)^{m+1}H(y).
$$
These representations exist for reciprocal polynomials of the given nominal degrees. Subtracting the lowest coefficient times $t^j(1+t)^{m-2j}$ successively constructs them. The leading coefficient of $G$ can be different from one. On each noncentral root the chain rule gives $D(t)=(1+t)^{m+1}y(1-4y)G'(y)$. Each distinct root of $G$ represents one noncentral orbit. Define
$$
B=H\,[y(1-4y)G']^{-1}\pmod G.
$$
The inverse exists because these roots are simple, negative, and different from $0$. Lagrange interpolation of the remainder $G'B^2\bmod G$ gives the noncentral sum exactly as

$$
\sum_{G(s)=0}B(s)^2
=\frac{[y^{\deg G-1}](G'B^2\bmod G)}{\mathrm{lc}(G)}.
$$

Indeed the leading coefficient of the interpolation polynomial is the sum of its values times $\mathrm{lc}(G)/G'(s)$. A constant $G$ gives an empty sum.

An independent checker instead writes reciprocal polynomials in $w=t+1/t$. It solves an integer multiplication-matrix system over the rationals and takes the trace of the square of multiplication by the quotient. The two calculations agree entry by entry on every pair with nonzero lag and new size at most 46. There are 441 such pairs. The largest $S$ is $25/36$, attained only at $(n,k)=(5,3)$, where $n$ is the old size. The archive retains every exact rational value. Both methods use the previously certified original coefficient archive. At the declared review point the test supplied a sufficient inequality and supported it on the existing range. Further work requires an estimate at the noncentral roots. [Rational traces](squared-traces.jsonl.gz) · [Quotient-polynomial checker](verify_residue_traces.py) · [Independent matrix checker](verify_companion_traces.py)

Run these commands with Python and python-flint 0.9.0 from the topic folder.

~~~sh
python3 -I -O verify_residue_traces.py
python3 -I -O verify_companion_traces.py insertion-lag.jsonl.gz squared-traces.jsonl.gz
~~~
