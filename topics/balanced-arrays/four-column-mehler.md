# An elliptic-curve generating function for four balanced columns

Let $a_{n,k}$ count labeled binary arrays with $n$ rows, four columns of sum $k$, and row cap two. Put $\delta=n-2k$ and
$$
H_{n,k}=\frac{(k!)^2\delta!}{n!}a_{n,k},\qquad H_n(q)=\sum_{k=0}^{\lfloor n/2\rfloor}H_{n,k}q^k.
$$
The problem asks for real-rootedness of $\sum_k a_{n,k}q^k$ for every $n$. This note reduces it to a stronger integer family with a rank-three rational differential system. It gives no all-row root count. [Original U(2,4) challenge](https://github.com/PerAlexandersson/RealRooted/issues/2005)

## Reduction to a Mehler kernel

Write $He_k$ for the probabilists' Hermite polynomial, defined by
$$
e^{yu-u^2/2}=\sum_{k\ge0}He_k(y)u^k/k!,
$$
and let $Z$ be a standard normal variable. If $R=1+e_1(x)+e_2(x)$ in four variables, the normal moment generating function gives
$$
e^{vR(x)}=e^v\,\mathbb E\prod_{i=1}^4 \exp\big((\sqrt v Z+v)x_i-vx_i^2/2\big).
$$
Indeed $e_2=((\sum_i x_i)^2-\sum_i x_i^2)/2$. Extracting the four equal exponents gives
$$
\sum_{n\ge2k}\frac{a_{n,k}}{n!}v^{n-2k}
=\frac{e^v}{(k!)^4}\mathbb E He_k(Z+\sqrt v)^4.
$$
The expectation is a polynomial in $v$ by symmetry of $Z$ and parity of $He_k$.

Mehler's formula, using $He_k(y)=2^{-k/2}H_k^{\rm phys}(y/\sqrt2)$, gives
$$
\sum_{j\ge0}\frac{He_j(y)^2}{j!}z^j
=\frac{\exp(y^2z/(1+z))}{\sqrt{1-z^2}}.
$$
Multiply this formula at $z,w$ and take expectation at $y=Z+\sqrt v$. For $A=z/(1+z)+w/(1+w)$, use
$\mathbb E e^{A(Z+\sqrt v)^2}=(1-2A)^{-1/2}\exp(vA/(1-2A))$. Thus
$$
e^v\sum_{i,j\ge0}\frac{\mathbb E [He_i(Z+\sqrt v)^2He_j(Z+\sqrt v)^2]}{i!j!}z^i w^j
=\frac{\exp(v(1-zw)/D)}{\sqrt{UD}},
\quad U=(1-z)(1-w),\quad D=1-z-w-3zw.
$$
All manipulations hold coefficientwise in $z,w$ or on a sufficiently small complex neighborhood. In particular,
$$
H_{2k+\delta,k}=[z^k w^k]\frac{(1-zw)^\delta}{\sqrt U D^{\delta+1/2}}.\tag{1}
$$
[Mehler's formula](https://dlmf.nist.gov/18.18.E28)

A positive finite formula follows by expanding $D=U-4zw$. Put $h=k-j$ and $m=\delta+j$ inside the summation below. Then
$$
H_{2k+\delta,k}
=\sum_{j=0}^k \frac{4^j(\delta+1/2)_j}{j!}
\sum_{s=0}^{\min(h,m)} \binom ms^2\binom{\delta+2j+h-s}{h-s}.\tag{2}
$$
In fact the remaining diagonal after choosing $(4zw)^j$ is the coefficient of $Q^h$ in
$(1-Q)^\delta\sum_{a\ge0}\binom{m+a}{a}^2Q^a$. Euler's hypergeometric transformation identifies this with the corresponding coefficient of $(1-Q)^{-\delta-2j-1}\sum_{s=0}^m\binom ms^2 Q^s$. The prefactors $4^j(\delta+1/2)_j/j!$ are integers since their generating function in $j$ is $(1-4x)^{-\delta}(1-4x)^{-1/2}$. Every $H_{n,k}$ on its support is therefore a positive integer. [Euler's hypergeometric transformation](https://dlmf.nist.gov/15.8.E1)

## One contour and a rational differential system

Summing (1) over $\delta$ gives

$$
\sum_{\delta,k\ge0}H_{2k+\delta,k}t^\delta Q^k
=\mathrm{CT}_z\\, \frac{\sqrt D}{\sqrt U\\,[D-t(1-Q)]}\bigg|_{w=Q/z}.
$$

Take $Q=qt^2$ to get $G(t,q)=\sum_{n\ge0}H_n(q)t^n$. Use the following notation for the contour integral:
$$
A_0=1+Q,\quad B_0=1-3Q,\quad h=t(1-Q),\quad C=B_0-h,\quad
P(x)=(x^2-4Q)(x-A_0)(x-B_0),\quad Y^2=P(x).
$$
The change of variable $x=z+Q/z$ gives
$$
G(t,q)=\frac1{2\pi i}\oint\left(1-\frac h{x-C}\right)\frac{dx}{Y}.\tag{3}
$$
For example, take real $q>0$ and positive $t$ sufficiently small, and start with the circle $|z|=\varepsilon$ for fixed small $\varepsilon$. Its image surrounds the interval between $-2\sqrt Q$ and $2\sqrt Q$ counterclockwise and excludes $A_0,B_0,C$. There $dx/\sqrt{x^2-4Q}=dz/z$ with the branch $\sqrt{x^2-4Q}=z-Q/z$. Take the other square root from its value at $t=0$ near $x=0$. This proves (3) by the formal constant-term identity or by analytic continuation from this open domain. The lifted contour is closed on the curve. Around a nonsingular parameter value the contour can be taken fixed in $x$, since the moving branch points and marked poles stay away from it.

For generic $(t,q)$, $P$ is squarefree and $P(C)\ne0$. Let $p_3=-2(1-Q)$ be its cubic coefficient. The three periods needed are the integrals of $R_j,dx/Y$ over the same cycle, divided by $2\pi i$, for
$$
R_0=1,\qquad R_1=x^2+p_3 x/2,\qquad R_2=1/(x-C).
$$
They satisfy the following explicit rational connection algorithm, with dots indicating $t$-differentiation at fixed $q$ and primes indicating $x$-differentiation. For a chosen $R=R_j$, start with $T=\dot R-R\dot P/(2P)$. Set $V=0$ for $j=0,1$, and $V=-\dot C/(x-C)$ for $j=2$. Subtract the exact differential $d(V/Y)$, which at $C$ removes the double pole coming from $\dot R_2$. Solve the polynomial congruence
$$
W P' \equiv R\dot P-VP'\pmod P,\qquad \deg W<4.\tag{4}
$$
Here rational denominators $x-C$ are invertible modulo $P$, and $P'$ is invertible because $P$ is squarefree. Subtract the additional exact differential $d(W/Y)$. The remaining rational numerator is
$$
S=T-(V+W)'+(V+W)P'/(2P).
$$
Congruence (4) kills its poles at the roots of $P$. It has at most a simple pole at $C$ and its polynomial part has degree at most two by degree counting at infinity. The differential $S\,dx/Y$ has zero residues at both points over infinity. To see this, each original differential $R_j\,dx/Y$ has that property by the choice of $p_3/2$, differentiation at fixed coordinate $x$ preserves the vanishing Laurent coefficient, and exact differentials have zero residue. Thus the coefficient of $x$ in the polynomial part of $S$ is $p_3/2$ times that of $x^2$. Consequently $S$ is a rational linear combination of $R_0,R_1,R_2$. Its coefficients are a row of the three-by-three connection. Every step uses only Euclidean polynomial division over $\mathbb Q(t,q)$.

Writing the three periods as a vector $I$, this gives $\partial_t I=M(t,q)I$ with rational $M$, and $G=I_0-hI_2$. Thus $G,\partial_t G,\partial_t^2G,\partial_t^3G$ satisfy a linear dependence over $\mathbb Q(t,q)$. Clearing denominators yields a scalar differential equation of order at most three and hence an exact finite-band linear recurrence with polynomial coefficients in $n,q$ for the $H_n$. This establishes the order bound without searching for recurrences. It does not establish positivity of the connection or a Sturm recurrence.

The endpoint singularities in (3) also simplify explicitly. With $u^2=q$, the moving pole meets a branch point $x=\pm2ut$ on
$$
1-t-3u^2t^2+u^2t^3\mp2ut
=(1\pm ut)(1-t\mp3ut\pm ut^2).
$$
The branch-point collisions with $x=A_0$ and $x=B_0$ respectively occur on $(1\mp ut)^2=0$ and $(1\pm ut)(1\mp3ut)=0$. This factorization identifies possible competing singularities; it gives no finite-$n$ coefficient signs by itself.

For $q=-a^2<0$, take $u=ia$. The quadratic $1-(1+3ia)t+ia t^2$ has exactly one root in $|t|<1/(3a)$. Substitute $\xi=3ia t$ and $\epsilon=1/(9a)$ to get $1-\xi+i\epsilon\xi(3-\xi)$. On $|\xi|=1$ the real part of $(1-\xi)/(\xi(3-\xi))$ is
$$
\frac{-2(\cos(\arg\xi)-1)^2}{|3-\xi|^2}.
$$
It vanishes only at $\xi=1$, where the ratio is zero, so there is no boundary zero for $\epsilon>0$. For $\epsilon>1$, Rouché's theorem gives one inside $|\xi|=1$, by comparison to $i\epsilon\xi(3-\xi)$. The root count is constant for all $\epsilon>0$. The conjugate quadratic gives the conjugate root in the same disk. This is a statement about the collision equation. Proving an effective coefficient sign count from the period requires further analysis.

## The two local limits of the stronger family

At the origin,
$$
H_n(w/n^2)\longrightarrow\sum_{k\ge0}\frac{w^k}{(k!)^2}
$$
locally uniformly. For fixed $k$, $a_{n,k}/\binom nk^4\to1$ by the union bound $4n(k/n)^3$ on triple occupancy. For uniform domination, the ratio of the $k$th rescaled coefficient to $1/(k!)^2$ is bounded by
$$
\frac{(n)_{\underline{k}}^4}{(n)_{\underline{2k}}n^{2k}}
\le\frac{(n)_{\underline{k}}}{(n-k)_{\underline{k}}}
\le\binom{2k}{k}\le4^k
$$
for $k\le n/2$. The ratio in the middle decreases in $n$, so its maximum occurs at $n=2k$.

At the opposite end let $m=\lfloor n/2\rfloor$, $s=n-2m\in\{0,1\}$, and $\gamma=2/3$. Along each parity class the reversed limit is
$$
\sum_{j=0}^m \frac{H_{n,m-j}}{H_{n,m}}\left(\frac{4w}{\gamma^4 n^2}\right)^j
\longrightarrow W_s(w)=\sum_{j\ge0}\frac{w^j}{(s+1/2)_{2j}}
\tag{5}
$$
locally uniformly. Here are details for the required coefficient bounds. A row of size two has six choices, a row of size one has four, and an empty row has one. The number of rows deficient by one or two, weighted without enforcing the column quotas, is
$$
6^n[z^E](1+\gamma z+z^2/6)^n,\qquad E=2s+4j.
$$
For fixed $E$ the main term is $6^n\gamma^E n^E/E!$, from $E$ rows of deficiency one. After fixing the bounded number of deficient rows, independent size-two rows have a common lattice local central limit factor $c n^{-3/2}$ to realize the balanced margins. Projecting to the first three columns gives a nonsingular covariance and a full span, since differences of size-two atoms include the three standard basis vectors. Remaining target shifts are bounded for fixed $E$, so the factor is the same for every fixed $E$. Fourier inversion also gives a bound $C(M+1)^{-3/2}$ at any point for the sum of $M$ independent size-two rows. Away from the origin their characteristic function has modulus bounded strictly below one by the full span, and near the origin it has a Gaussian bound by nonsingular covariance. These are the fixed-rank endpoint estimates applied here. [Fixed-rank endpoint proof](https://github.com/ProgramComputer/open-math-research/blob/main/topics/balanced-arrays/fixed-rank-edges.md)

In particular the unnormalized coefficient ratio tends to $(\gamma n)^{4j}(2s)!/(2s+4j)!$ in relative error for fixed $j$. Multiplying by $(m-j)!^2(s+2j)!/(m!^2s!)$ and using
$$
\frac{(2s)!(s+2j)!}{s!(2s+4j)!}=\frac{16^{-j}}{(s+1/2)_{2j}}
$$
gives the indicated limit. For domination, choosing $b$ rows of deficiency two and $E-2b$ of deficiency one bounds the coefficient of $z^E$ by
$$
[z^E](1+\gamma z+z^2/6)^n
\le\frac{(\gamma n)^E}{E!}
 \exp\left(\frac{E^2}{6\gamma^2 n}\right).
$$
Indeed the individual term in the exponential tail estimate follows from $(n)_{\underline{E-b}}\le n^{E-b}$ and $(E)_{\underline{2b}}\le E^{2b}$. Since $E\le2n$, the exponential is at most $C_1^E$. When $E\le n/2$ at least $n/2$ rows have size two and the ratio to the local central factor is uniformly bounded. When $E>n/2$ the same ratio is at most $Cn^{3/2}\le C(2E)^{3/2}$. Finally $(m)_{\underline j}\ge(m/e)^j$ for $j\le m$, by comparison of the geometric mean of its largest $j$ factors to that of all $m$ factors. Together these bounds give a uniform majorant of the form $C_2^{j+1}(j+1)^{3/2}/(s+1/2)_{2j}$ for the powered coefficients in (5), which suffices on every compact disk.

The odd upper limit is the Fourier cosine transform
$$
W_1(-v^2)=\frac12\int_0^1(1-t)^{-1/2}\cos(vt)\,dt.
$$
Pólya's theorem for positive increasing integrable kernels gives only simple real zeros in $v$, hence simple negative zeros of $W_1(w)$. Since $W_1$ has order $1/2$ in $w$, its product has genus zero. Moreover $W_0=(1+4w\partial_w)W_1$. The logarithmic derivative quotient is strictly monotone between the poles and gives exactly one simple real zero closer to zero than the first pole and one between each consecutive pair of poles. For complex $w$ the imaginary part of $W_0/W_1=1+4\sum_j w/(w+b_j)$ has the sign of $\Im w$, where $-b_j$ are the zeros of $W_1$. Thus its whole zero set is real and the two upper limits strictly alternate. Hurwitz's theorem transfers any fixed number of upper roots to the corresponding parity subsequences for large $n$. It gives no simultaneous control of the growing middle. [Pólya's cosine-transform theorem, original citation and statement](https://www.dcce.ibilce.unesp.br/~dimitrov/ProfRusev/EJA_Paper_24_02_11/Dim_Rus_main.pdf)

## Sufficiency for the unnormalized array and exact boundary

The twice-binomial-normalized coefficient is
$$
\frac{a_{n,k}}{\binom nk^2}
=H_{n,k}\frac{\binom{n-k}k}{\binom nk}
=H_{n,k}4^k\prod_{A\in\{n/2,(n-1)/2\}}\frac{\binom Ak}{\binom nk}.
$$
For $m=\lfloor n/2\rfloor$, each ratio is a finite multiplier preserving real nonpositive zeros up to degree $m$. To verify its symbol, reverse the degree-$m$ polynomial with coefficients $\binom mj\binom Aj/\binom nj$ and divide by its resulting constant coefficient. The resulting polynomial is
$$
\sum_{j=0}^m\binom mj\frac{(n-m+1)_j}{(A-m+1)_j}q^j
=\frac{P_m^{(A-m,n-A-m)}(1+2q)}{\binom A m}.
$$
Both Jacobi parameters exceed $-1$, so its zeros are in $(-1,0)$. The unreversed symbol has negative zeros. Finite Schur–Szegő composition proves the multiplier claim. Multiplication by $4^k$ rescales the variable, and multiplication by $\binom nk$ twice is also a finite negative-root-preserving multiplier. The symbol of the latter multiplier is $\sum_k\binom mk\binom nk q^k=(1-q)^m P_m^{(0,n-m)}((1+q)/(1-q))$ by Pfaff's transformation, and its zeros are negative. Hence all-row real-rootedness for $H$ would imply the author's conjecture for $U(2,4)$. [Jacobi hypergeometric form](https://dlmf.nist.gov/18.5.E7) · [Finite Schur–Szegő composition](https://www.numdam.org/item/CRMATH_2008__346_5-6_271_0.pdf)

There is no ordinary monic scalar three-term Favard recurrence for the even subsequence. The first rows are $1$, $1+3q$, $1+17q+15q^2$, and $1+39q+229q^2+93q^3$. Write their monic versions as $p_0,p_1,p_2,p_3$. Matching the $q^2$ and $q$ coefficients in $p_3=(q+A)p_2+Bp_1$ forces $A=206/155$ and $B=-894/775$. The remaining constant difference is $23/75$.

The standalone checker compares (2) to the independent column-pair count and certifies an exact simple negative root count and the oriented interlacing of consecutive rows over the supplied finite prefix. Run:
```sh
python3 -I topics/balanced-arrays/code/verify_four_column_mehler.py --through 120 --jsonl > /tmp/four-column-mehler-replay.jsonl
```

Compare the replay with the [archived rows](results/four_column_mehler.jsonl). The exact checks cover 3,721 coefficients, 121 rows and 120 consecutive pairs.
