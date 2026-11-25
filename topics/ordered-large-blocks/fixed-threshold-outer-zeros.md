# The largest zeros at every fixed ordered threshold

Fix $j\ge2$. Write $A_{n,k}=[t^k]O_{n,j}(t)$ and $n=jm+s$, $0\le s<j$. Set
$$
 \alpha=1+\frac1{j+1},\quad L_m=j!\,(\alpha m)^j,\qquad
 H_s(x)=\sum_{h\ge0}\frac{x^h}{(jh+s)!}.
$$
Let $0<\lambda_{s,1}<\lambda_{s,2}<\cdots$ be the moduli of the negative zeros of $H_s$.

**Theorem.** For every finite $K$, the $K$ largest-modulus complex zeros of $O_{n,j}$ are simple and negative for all sufficiently large $n$. Their moduli $Q_{n,1}>\cdots>Q_{n,K}$ satisfy $Q_{n,i}/L_m\to1/\lambda_{s,i}$ along each residue $s$. They strictly alternate with those in the next row at this end. With indices within the fixed range, the order for $s<j-1$ is
$$
 Q_{n,i}>Q_{n+1,i}>Q_{n,i+1},
$$
and for $s=j-1$ it is
$$
 Q_{n+1,i}>Q_{n,i}>Q_{n+1,i+1}.
$$
This conclusion allows every fixed threshold and unbounded row size. It describes the outermost complex zeros even if real-rootedness of the remaining polynomial is unknown.

**Proof.** Write $S(z)=\sum_{a=1}^{j-1}z^a/a!$ and $C(z)=\sum_{a\ge j}z^a/a!$. Let $T=1/(1-S)$ and $W=j!z^{-j}C T$, analytic at zero. The ordered-block generating function gives
$$
 A_{n,k}/n!=(j!)^{-k}[z^{n-jk}]\,T(z)W(z)^k .
$$
This coefficient extraction also appears in the [prior research note](https://github.com/1337isnot1337/solved-conjectures/blob/main/research/alexandersson-ordered-set-partitions/PROGRESS.md). The functions $T$ and $W$ have nonnegative coefficients, constant term one, and $W'(0)=\alpha$. For fixed $h,e\ge0$,
$$
 m^{-e}[z^e]T(z)W(z)^{m-h}\longrightarrow \alpha^e/e!.
$$
Indeed $T(w/m)W(w/m)^{m-h}\to e^{\alpha w}$ locally uniformly in $w$ since $\log W(z)=\alpha z+O(z^2)$ near zero. Applying coefficient convergence at $e=s+jh$ and at $e=s$ gives
$$
 \frac{A_{n,m-h}}{A_{n,m}L_m^h}\longrightarrow \frac{s!}{(s+jh)!}.
$$

The convergence holds for the whole reversed polynomial locally uniformly. For any fixed $B>0$, the nonnegative coefficients and evaluation at $z=B/m$ bound
$$
 m^{-e}[z^e]T(z)W(z)^{m-h}
 \le B^{-e}T(B/m)W(B/m)^m\le C_B B^{-e}
$$
for $0\le h\le m$ and sufficiently large $m$. Also $m^{-s}[z^s]T(z)W(z)^m$ stays bounded below by a positive constant. Taking $B$ arbitrarily large therefore gives a summable geometric majorant on each compact disk for the terms of
$$
 \mathcal R_{m,s}(x)=\sum_{h=0}^m\frac{A_{n,m-h}}{A_{n,m}L_m^h}x^h
 \ \longrightarrow\ s!H_s(x).
$$
These are the exponential-series sections. The Gauss multiplication formula writes $s!H_s$ as a hypergeometric ${}_0F_{j-1}$ at $x/j^j$, with the positive parameters $(s+1)/j,\ldots,(s+j)/j$ and the single parameter $1$ removed. The hyper-Bessel zero theorem puts all its zeros on the negative real axis. The series has order at most $1/j<1$ and is nonpolynomial, so Hadamard factorization gives infinitely many zeros and a genus-zero product. [Baricz and Singh, Theorem 2](https://arxiv.org/abs/1702.00626)

Here is a short proof of the strict ordering needed in the transfer. For $s>0$, $H_{s-1}=(jx\partial_x+s)H_s$, while $H_{j-1}=jH_0'$. At a negative zero of multiplicity $b$ either operation lowers its multiplicity by one. At points $x<0$ where the input is nonzero, a newly created zero is simple, since
$$
 \left(\frac{H_s'}{H_s}+\frac{s}{jx}\right)'=-\sum_{H_s(y)=0}\frac{1}{(x-y)^2}-\frac{s}{jx^2}<0 .
$$
For the derivative step take $s=0$. Traversing the whole cycle returns to the original function, contradicting an initial multiplicity greater than one: it either decreases throughout, or drops to at most one and can never exceed one again. Thus all zeros are simple. In each gap between successive input zeros the displayed logarithmic expression decreases from positive to negative infinity. In the rightmost gap ending at zero it has a unique zero for $s>0$ and none for $s=0$, by the genus-zero product. These relations give $\lambda_{s-1,i}<\lambda_{s,i}$ and $\lambda_{j-1,i}<\lambda_{0,i+1}$, hence $\lambda_{0,i}<\cdots<\lambda_{j-1,i}<\lambda_{0,i+1}$.

Choose a large disk containing the first $K$ limit zeros and no further zero, then disjoint smaller disks centered on them. Rouché's theorem on all these boundaries gives one simple zero in each small disk and exactly $K$ zeros in the larger one for all large $m$. Conjugation gives reality. Reversing takes a zero $x$ to $L_m/x$. The strict inequalities between section zeros and $L_{m+1}/L_m\to1$ give both consecutive orders, including the degree increase at the residue wrap. There are only $j$ residues. At $j=2$ these constants agree with the [two explicit parity formulas](root-law.md). $\square$
