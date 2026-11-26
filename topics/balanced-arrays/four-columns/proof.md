# Real-rootedness for four balanced columns with row cap two

**Theorem.** For every integer $n\ge0$, let $a_{n,k}$ count the labeled binary $n\times4$ arrays with all four column sums equal to $k$ and all row sums at most two. The polynomial
$$
P_n(q)=\sum_{k\ge0}a_{n,k}q^k
=\sum_{k\ge0}[x_1^k x_2^k x_3^k x_4^k](1+e_1(x)+e_2(x))^n q^k
$$
has exactly $\lfloor n/2\rfloor$ distinct negative zeros. For $n=0,1$ it equals 1.

This is the $(r,d)=(2,4)$ specialization of Per Alexandersson’s conjecture on balanced arrays of uniform matroids. All allowed row supports carry unit weight. The conjecture for arbitrary $(r,d)$ remains open, and consecutive interlacing is a separate question. The [literature record](literature.md) discusses prior computations and the author’s reported eventual claim. [SymCat, “Balanced arrays of uniform matroids”](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Alexandersson’s statement and counting formula](https://github.com/PerAlexandersson/RealRooted/issues/2005)

## Degree and coefficient formula

The constant coefficient is 1. An array of quota $k$ has $4k$ ones, so $k\le\lfloor n/2\rfloor$. For each quota in that range one can take $k$ rows of type $1100$ and $k$ rows of type $0011$, with the remaining rows zero. Thus $P_n$ has degree $d_n=\lfloor n/2\rfloor$ and positive coefficients through that degree. In particular, $P_n(-t^4)$ has sign $(-1)^{d_n}$ for all sufficiently large $t$.

Let $M_{k,p}$ count the $p$-edge matchings of the complete four-partite graph with $k$ vertices per color. Label the $k$ ones in each column separately. Each row containing two ones induces a matching edge between labels from different colors. The $p$ edges and the $4k-2p$ unmatched vertices give $4k-p$ blocks to inject into the $n$ labeled rows. This is a bijection for labeled ones, and each array has $(k!)^4$ such labelings. Hence
$$
a_{n,k}=\frac{1}{(k!)^4}\sum_{p=0}^{2k} M_{k,p}(n)_{4k-p},
\qquad
(x)_s=\prod_{h=0}^{s-1}(x-h).
\tag{1}
$$
If $s>n\ge0$, then $(n)_s=0$. The matching counts can be computed from the empty graph by appending one color at a time. For an old matching with $p$ edges on $c$ colors, there are $ck-2p$ unused old vertices. Appending $i$ edges to the new color has $\binom{ck-2p}{i}\binom{k}{i}i!$ choices. The restriction of the resulting matching to the old colors is unique.

## The finite range

For $0\le n\le532$, the [finite certificates](certificates/rows/) give positive dyadics $0<t_1<\cdots<t_{d_n-1}$ when $d_n\ge2$ with
$$
\mathrm{sgn}\,P_n(-t_j^4)=(-1)^j.
$$
The [independent integer checker](code/independent_prefix.py) reconstructs all coefficients from (1) and the color-class recurrence. It checks the coefficient rows, node order and count, and evaluates every sign by integer Horner evaluation. At a reduced rational argument $q=A/B$ with $B>0$, the evaluated integer is $B^{d_n}P_n(A/B)$. The [producing checker](code/prefix.py) uses an independent inclusion–exclusion matching count and rigorous Arb evaluation with exact integer fallback. The [finite-prefix review](review/prefix.md) describes the derivations and replay results.

The sign at $t=0$ is positive and the sign at a sufficiently large finite $t$ is $(-1)^{d_n}$. Continuity gives $d_n$ distinct roots in the intervening open intervals, including the single interval between these endpoints if $d_n=1$. There are no roots when $d_n=0$. Since $t\mapsto-t^4$ is injective for $t>0$, the degree forces exactly $d_n$ simple negative roots.

## Forty lower roots for every $n\ge533$

### A decreasing alternating tail

For adjacent quotas, double-count a quota-$k+1$ array together with a choice of one of its occupied positions to delete in each column. There are $(k+1)^4$ choices in every such array. Removal preserves the row cap and gives a quota-$k$ array. The remaining array and the four deletion row indices, in column order, determine the starting array and all four choices uniquely. There are at most $n^4$ tuples of deletion rows for each remaining array, allowing equal indices for different columns. Thus
$$
(k+1)^4 a_{n,k+1}\le n^4 a_{n,k}.
\tag{2}
$$
For $b_k=a_{n,k}t^{4k}$, this gives $b_{k+1}\le (nt/(k+1))^4 b_k$. If $nt<M+1$, the magnitudes are nonincreasing for $k\ge M$, including all coefficients beyond the degree, which vanish. Pairing consecutive terms of the alternating tail after $M$ gives
$$
\sum_{k=0}^M(-1)^k b_k\le P_n(-t^4)\quad(M\text{ odd}),\qquad
P_n(-t^4)\le\sum_{k=0}^M(-1)^k b_k\quad(M\text{ even}).
\tag{3}
$$

### A simultaneous integer certificate

Set $n_0=533$. For $1\le j\le40$, the [lower certificate](certificates/lower.jsonl) specifies integers $y_j,s_j,M_j$ and uses the node
$$
t_j(n)=\frac{y_j}{16n-s_j}.
$$
The list has strictly increasing positive $y_j$ and $s_j$, and $16n_0>s_j$ in every record. Hence the nodes are positive and strictly increasing for every $n\ge n_0$. The certificate uses $M_j$ of parity opposite to $j$ and verifies
$$
(M_j+1)(16n_0-s_j)>n_0 y_j.
$$
The function $n/(16n-s_j)$ decreases for $n\ge n_0$ since $s_j>0$. Therefore $nt_j(n)<M_j+1$ throughout this range, and (3) applies.

To check each truncated sum at once for all these rows, fix a record $(j,y,s,M)$ and set $X=n-n_0$. Put $D=16(n_0+X)-s$ and
$$
R_k(X)=\sum_p M_{k,p}(n_0+X)_{4k-p}\in\mathbb Z[X].
$$
The checker constructs $A_{-1}=0$ and step by step constructs
$$
A_k = D^4 A_{k-1}+(-1)^k y^{4k}\frac{(M!)^4}{(k!)^4}R_k(X)
\quad (0\le k\le M).
$$
Induction gives
$$
A_k=\sum_{h=0}^{k}D^{4(k-h)}(-1)^h y^{4h}\frac{(M!)^4}{(h!)^4}R_h(X).
$$
Thus at $X=n-n_0$,
$$
A_M(X)=(M!)^4 D^{4M}\sum_{k=0}^M a_{n,k}(-t_j(n)^4)^k.
\tag{4}
$$
The multiplier is positive. The [lower checker](code/lower.py) uses exact integer polynomial arithmetic and reports zero coefficients of the wrong sign or equal to zero among degrees $0$ through $\deg A_M$ in $(-1)^j A_M$. Each has positive constant term, so its value is strictly positive at every $X\ge0$. This proves the sign of the truncated sum. By its parity and (3), the sign of $P_n(-t_j(n)^4)$ is exactly $(-1)^j$. The sign at zero is positive, so the forty intervening intervals contain forty distinct roots and the value at $t_{40}(n)=718/(16n-507)$ is strictly positive.

## Phase signs on the rest of the positive axis

Let $\zeta=e^{i\pi/4}$ and, for $t>0$, define
$$
S=1+4\zeta t+6it^2,\qquad
\Lambda=\frac{2\zeta t+4it^2}{S},\qquad
\Psi_n(t)=n\arg S-\frac32\arg\Lambda,\qquad
C_n=\frac{(\pi n|\Lambda|)^{3/2}}{|S|^n}.
$$
The arguments are principal. The [central calculation](central.md) proves $\Re\Lambda>0$, gives the normalized torus integral on two copies of the angular domain, and bounds its difference from the real part of one complex Gaussian. In particular, the phase is continuous for $t>0$. For any $n\ge533$, the following ranges give sign $(-1)^j$ whenever $\Psi_n(t)=j\pi$ and $0\le j\le d_n-1$.

- For $0<t\le1/5$ and $nt\ge40$, the [small-parameter estimate](small.md) bounds $|C_nP_n(-t^4)-\cos\Psi_n|$ by $2/5$. It uses sharper local damping on successive radial regions and the angular averages of the quartic and squared cubic errors.
- For $1/5\le t\le38/7$, the compact calculation below bounds the same error by $33827/100000$.
- For $t\ge38/7$, the [upper estimate](upper.md) uses the opposite-pair coordinates and retains the contribution of both positive-half saddle values. Its conclusion applies directly at the designated nodes.

### The compact interval

Use $Q=|p|^2$ in the central integral. Retain the precise positive rates, writing $H=|\Lambda|$ and $L=\Re\Lambda$. The rates and error constants from the central calculation are
$$
\begin{aligned}
a&=\frac{3(4\sqrt2t/9+16t^2/3+16\sqrt2t^3/3+16t^4)}{\pi^2|S|^2},
& a_0&=\frac{37}{50}L,\\
B_0&=\frac{t/2+4t^2/3}{|S|}+\frac{H^2}{2},
&K_0&=\frac{4t}{3\sqrt3|S|},\\
b&=\frac{2\sqrt2t+12\sqrt2t^3}{|S|^2}.
\end{aligned}
$$
The last expression is the lower relative squared-modulus gap for the minus cube before simplifying it to a coarser rate. Averaging it with the original global radial gap gives $|R_-/S|\le e^{-aQ/2-b/4}$.

For $x\ge0$ put
$$
G(x)=\mathrm{erfc}(\sqrt{x})+2\sqrt{x/\pi}\,e^{-x}.
$$
The full-space radial Gaussian tail beyond $Q=1/4$ for rate $nr$ is $(\pi/(nr))^{3/2}G(nr/4)$. This follows by one integration by parts on $\int_{\sqrt{nr/4}}^\infty s^2e^{-s^2}\,ds$. Combining the local error on $Q\le1/4$, the actual plus tail, the comparison Gaussian tail, and the minus integral, in that order, gives
$$
\begin{aligned}
|C_nP_n(-t^4)-\cos\Psi_n|
\le {}&
\frac{21}{20}\frac{(H/a_0)^{3/2}}{n a_0}
  \left(\frac{15B_0}{4a_0}+\frac{105K_0^2}{16a_0^2}\right)\\
&+\left(\frac H a\right)^{3/2}G(na/4)
 +\left(\frac H L\right)^{3/2}G(nL/4)
 +\left(\frac{2H}{a}\right)^{3/2}e^{-nb/4}.
\end{aligned}
\tag{5}
$$
Here $n\ge533$ ensures the local loss factors are at most $21/20$. The positivity of the rates, together with the decreasing Gaussian exterior fraction $G$, shows each term is nonincreasing in $n$ for fixed $t$. The [compact interval checker](code/middle.py) evaluates (5) at $n=533$ with Arb enclosures on 2,048 closed rational subintervals covering $[1/5,38/7]$. All upper enclosures are at most $33827/100000<1/2$ in the recorded replay.

### The transition to node 41

For $u=1/n\in(0,1/533]$ set $\tau=nt_{40}=718/(16-507u)$ and $t_{40}=\tau u$. In the [same interval checker](code/middle.py), 64 closed rational subintervals covering $[0,1/533]$ verify
$$
\tau>40,\qquad t_{40}<1/5,\qquad \Psi_n(t_{40})<41\pi.
\tag{6}
$$
To see the last enclosure, set $t=t_{40}$, $h=(2\sqrt2+6t)/(1+2\sqrt2t)$, and $z=th$. Then
$$
\arg S=\arctan z,\qquad
\arg\Lambda=\frac{\pi}{4}+\arctan\left(\frac{\sqrt2t}{1+\sqrt2t}\right)-\arctan z.
$$
As $0\le z<1$, the alternating expansion gives $\arctan z\le z(1-z^2/3+z^4/5)$. The expression checked by the code is the resulting upper bound $\tau h(1-z^2/3+z^4/5)-(3/2)\arg\Lambda$ on the phase. This expression also has a well-defined limit at the enclosed endpoint $u=0$.

As $t\to\infty$, $\arg S\to\pi/2$ and $\Lambda\to2/3$, so $\Psi_n(t)\to n\pi/2>(d_n-1)\pi$. Starting at $t_{40}$, choose a finite point beyond it at which the phase exceeds $(d_n-1)\pi$. By continuity, there is a point strictly between them of phase $41\pi$. Starting from that point and using the same finite right endpoint, continuity supplies a later point of phase $42\pi$. Continuing produces strictly increasing points of phase $j\pi$ for $41\le j\le d_n-1$. This argument uses only continuity and the two endpoint inequalities.

Every such point has $nt>40$ by (6), so one of the three phase bounds applies. Thus the signs after $t_{40}$ are successively negative, positive, and alternating through $(-1)^{d_n-1}$. A final sufficiently large point has sign $(-1)^{d_n}$. The intervals following $t_{40}$ therefore contribute $d_n-40$ additional distinct roots. Along with the forty lower roots, these give $d_n$ distinct negative zeros, and the degree forces all to be simple. Together with the finite range, this proves the stated result.
