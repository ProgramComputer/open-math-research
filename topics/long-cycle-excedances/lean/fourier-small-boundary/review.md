# Independent review of the direct Cauchy boundary bound

Agent-assisted source review of commit `e5d16036f2dbfe7887f844385d7e77edffd126ae`. I found no discrepancy in the direct cutoff range, radius selection, normalization, or sign of the adjacent contrast. This review checks the boundary estimate conditional on the three stated original-numerator contractions. The production rebuild and the interior residue estimates are separate.

For $n\ge10000$ and $8\le k\le99$, the aspect $x=n/k$ exceeds $100$, so $c=\min(1/25,4/x)=4/x$. The squared gap is $c r^2/k=4r^2/n$. Setting $\delta=r/n$, one has $R\le(1+1/k)r\le9r/8$ and $\delta(2R+\delta)\le4r^2/n$. The conversion from squared-modulus gap to distance therefore holds even for poles outside the contour. In particular, no pole lies on the selected radius.

Independently, write $t=R/r$. The selected shift has $48/25\le a\le2$, giving $t^2=1+a/k\le5/4$ and $t\le9/8$. Consequently $t(t+1)\le19/8<12/5$, and

$$
1-\frac1t=\frac{a}{k t(t+1)}
\ge\frac{48/25}{(12/5)k}=\frac4{5k}.
$$

The inequality $\log(1/t)\le1/t-1$ now gives the claimed decay down to $k=8$ inclusive. The only lower-cutoff input in this calculation is $k\ge8$.

The two numerator comparisons refer to the same contracted norm and the original cutoff polynomial. With $nS^2\ge1$, one has $r\le\pi\sqrt n\le n$, and the angular displacement is at most $2r/k$. Thus the denominator loss $1+\Delta(1+\delta)/\delta$ is at most $1+4n/k\le n$. The principal period bound gives the inverse denominator factor $(1+r/k)/(r/k)$. Inserting these estimates yields $r\sup|f|/|T(p)|\le n(k+r)e^M\le2n^2e^M$.

The mode has modulus one, and $F_j$ is averaged over the full angular period. For $B=2n^2e^M|T(p)|/r$ and $W=r(r/R)^n/(2|T(p)|)$, one gets $W B=n^2e^M(r/R)^n$. The adjacent contrast has boundary factor $r/R$ on the successor mode and subtracts $(s/r)F_n$. This matches the original coefficient identity, and $|s/r|\le1$ and $r/R\le1$ give the factor two in its norm bound. There is no division by either polynomial row. The tilt at the principal pole is an exponential and has nonzero modulus, including at $s=0$.

For the stated scalar envelope, the conservative endpoint choices $(k,M)=(100,32),(50,60),(10,100)$ give $\frac45(n/k)-(M+13+30)$ at $n=10000$ equal to $5,57,657$. The derivative-free tangent estimate $\log n\le\log10000+n/10000-1$ preserves each margin because its contribution grows at slope $3/10000$ and each radial exponent grows at a greater slope. The conditions $e^{10}>10000$ and $e^{13}>130000$ follow from $e>27/10$. Hence the envelope is below $1/(100n)\le S/100$. The old bound is smaller than $1/25$, and twice the sine bound is smaller than $S/25$. The least cutoff eight belongs to the third branch, and the exact transitions at ten and fifty are covered.
