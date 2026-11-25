# Extreme zeros of the Eulerian matrix square

Let $e_{n,j}$ count permutations of $[n]$ with $j$ descents, and set $A(n,j)=e_{n,j-1}$ for $n\ge1$, with $A(0,0)=1$. This is the shifted Eulerian matrix in Mao–Wang’s Conjecture 4.1. Write $A_n(t)=\sum_j A(n,j)t^j$. For $n\ge1$ the $n$th row polynomial of the ordinary square is $xH_n(x)$, where

$$
H_n(x)=\sum_{k=1}^n A(n,k)\sum_{j=0}^{k-1}e_{k,j}x^j.
$$

The constant and leading coefficients of $H_n$ are $n!$ and $1$. Thus the row has a simple zero at $0$, and its other zeros are those of $H_n$. [Mao–Wang, §4](https://arxiv.org/html/2607.01572v1)

## Theorem

For each fixed positive integer $j$, the $j$th zero of $H_n$ in increasing order of modulus exists as a simple negative real zero $\alpha_{n,j}$ for all sufficiently large $n$. With $\rho_0=1$, $\rho_j=j/\log(j+1)$ for $j\ge1$, and $c_j=\rho_{j-1}/\rho_j$,

$$
\alpha_{n,j}\sim-c_j^{n+1},\qquad
\alpha_{n+1,j}>\alpha_{n,j}>\alpha_{n+1,j+1}
$$

for each fixed $j$ and all sufficiently large $n$.

For each fixed $h\ge1$, the $(2h-1)$st and $2h$th zeros in decreasing order of modulus exist as simple negative real zeros $\beta_{n,2h-1}$ and $\beta_{n,2h}$ for all sufficiently large $n$. Let

$$
a_h=h^{-(h-1)},\qquad b_h=(h+1)^{-(h-1)}+h^{-h},\qquad d_h=(h+1)^{-h},
$$

and let $\kappa_h^+>\kappa_h^->0$ be the two roots of $a_h v^2-b_h v+d_h$. Then

$$
\beta_{n,2h-1}\sim-\kappa_h^+\left(\frac{h+1}{h}\right)^n,
\qquad
\beta_{n,2h}\sim-\kappa_h^-\left(\frac{h+1}{h}\right)^n.
$$

For each fixed $k\ge1$ and all sufficiently large $n$,

$$
\beta_{n+1,k}<\beta_{n,k}<\beta_{n+1,k+1}.
$$

The modulus orderings count all complex zeros with multiplicity, so these conclusions do not require real-rootedness in advance. For instance, the rightmost nonzero zero is asymptotic to $-(\log 2)^{n+1}$ and the two farthest zeros have leading terms $-(1\pm1/\sqrt{2})2^n$. The theorem covers any fixed number of extreme zeros. The all-row conjecture and control of the remaining zeros are open in this investigation.

## Coefficient estimates and root localization

For $m\ge1$ and $j\ge0$, the Eulerian numbers satisfy

$$
0\le e_{m,j}\le(j+1)^m,
\qquad
e_{m,j}=\sum_{i=0}^j(-1)^i\binom{m+1}{i}(j+1-i)^m.
\tag{1}
$$

For the upper bound, sort the indices of a map $[m]\to[j+1]$ by value with ties broken by index. The resulting permutation has a strict value increase at each descent. Each permutation with exactly $j$ descents arises from exactly one such map, since the sorted labels must begin at $1$ and increase by one at every descent. More generally this construction for maps into $[q]$ gives $q^m=\sum_j e_{m,j}\binom{q+m-j-1}{m}$, taking the binomial to be zero for $q\le j$. Multiplying by $t^q$ and summing over $q\ge1$ gives $A_m(t)=(1-t)^{m+1}\sum_{q\ge1}q^m t^q$ for $|t|<1$. The alternating sum follows by extracting the coefficient of $t^{j+1}$. In particular, for fixed $j\ge1$,

$$
e_{m,j}=(j+1)^m+O_j\!\left((m+1)^j j^m\right),
\tag{2}
$$

and $e_{m,0}=1$.

Both endpoint arguments rescale a polynomial using a number $c\in(0,1)$, and divide its coefficients by a factor $U_nD^n$ with $D>0$. If $f_{n,j}$ are the original coefficients, a bound

$$
|f_{n,j}|\le U_n(j+1)g_j^n,\qquad \lim_{j\to\infty}g_j^{1/j}=1
$$

provides local uniform convergence of the normalized polynomials whenever the individual normalized coefficients converge. Indeed, for large enough $J$ and some $\eta>0$, $g_jc^j/D\le e^{-\eta j}$ for all $j\ge J$. On $|u|\le R$, the tail after substituting $x=c^n u$ is bounded by $\sum_{j\ge J}(j+1)(Re^{-\eta n})^j$, which tends to zero. Finite initial coefficients then give local uniform convergence. Coefficients past the degree can be extended by zero.

If the resulting limit is $u^r G(u)$ with $G(0)\ne0$ and distinct simple negative zeros, Rouché’s theorem applied to small, real-centered disks around those zeros gives exactly one zero in each such disk of the normalized real polynomial. Each zero is real by conjugation symmetry, is negative when its disk lies in the left half-plane, and is simple by the multiplicity count. Applying Rouché’s theorem also on circles centered at $0$ with radii between successive limiting moduli gives the exact modulus indices. The first such circle encloses $r$ zeros of the normalized polynomial if it lies inside the modulus of the first nonzero limit zero. This count treats the zeros tending to $0$ at the current scale with multiplicity.

## Zeros nearest zero

Write $p_{n,j}=[x^j]H_n(x)$. From (2) and the positivity of $A(n,k)$, for fixed $j\ge1$,

$$
p_{n,j}=A_n(j+1)+O_j\!\big((n+1)^j A_n(j)\big).
\tag{3}
$$

For $t>1$ the exponential generating function of the shifted Eulerian polynomials is

$$
\sum_{n\ge0} A_n(t)\frac{z^n}{n!}=\frac{1-t}{1-t e^{(1-t)z}}.
\tag{4}
$$

This follows by summing $A_n(t)=(1-t)^{n+1}\sum_{q\ge1} q^n t^q$ first for $|t|<1$ and $n\ge1$, adding $A_0=1$ and extending the identity coefficientwise in $z$. The nearest pole of (4) is the unique positive real pole $z_0=\log(t)/(t-1)$. Subtracting $1/(z_0-z)$ cancels it, and all other poles have strictly larger modulus. Cauchy’s coefficient bound on any circle with radius between the first and second pole moduli gives $A_n(t)/n!=z_0^{-n-1}+O_t(R_t^{-n})$ for some $R_t>z_0$.

The function $\rho(x)=x/\log(1+x)$ with $\rho(0)=1$ is strictly increasing and strictly log-concave on $[0,\infty)$. Its reciprocal is $\int_0^1(1+sx)^{-1}\,ds$, which strictly decreases. For each $s>0$ the integrand is strictly log-convex in $x$. The pointwise log-convex inequality followed by Hölder’s inequality gives strict log-convexity of the integral. Therefore $\rho_j>\rho_{j-1}$ and the ratios $c_j=\rho_{j-1}/\rho_j$ strictly increase in $(0,1)$. By (3) and (4), with $A_n(1)=n!$,

$$
\frac{p_{n,j}}{n!\rho_j^{n+1}}\longrightarrow1\qquad(j\ge0\text{ fixed}).
\tag{5}
$$

At scale $x=c_j^n u$, the sequence $\rho_i c_j^i$ in $i\ge0$ has a maximum $D=\rho_{j-1}c_j^{j-1}=\rho_jc_j^j$ at exactly $i=j-1,j$. This follows since the ratio of adjacent terms is $c_j/c_i$ for the pair $i-1,i$. Uniformly for every $i$, (1) gives $p_{n,i}\le A_n(i+1)\le n!(i+1)^n$. Hence the coefficient and tail estimates give the locally uniform limit

$$
\frac{H_n(c_j^n u)}{n!D^n}\longrightarrow
u^{j-1}(\rho_{j-1}+\rho_j u).
$$

The nonzero limit zero is $-c_j$. Localization gives the claimed asymptotic and modulus index. For fixed $j$, $|\alpha_{n+1,j}|/|\alpha_{n,j}|\to c_j<1$ and $|\alpha_{n,j}|/|\alpha_{n+1,j+1}|\to0$ since $c_j<c_{j+1}$. The zeros are negative, so these comparisons give the first interlacing inequality.

## Zeros farthest from zero

Put $L_n(z)=z^{n-1}H_n(1/z)$, and write $q_{n,i}=[z^i]L_n(z)$. Eulerian symmetry $e_{m,j}=e_{m,m-1-j}$, obtained by complementing permutation values, gives

$$
q_{n,i}=\sum_{b=0}^i e_{n,b}\,e_{n-b,i-b},\qquad 0\le i\le n-1.
\tag{6}
$$

Here the intermediate index of the matrix product is $n-b$. The exponential growth base for a fixed summand is $(b+1)(i-b+1)$. Let $M_i=\max_{0\le b\le i}(b+1)(i-b+1)=\lfloor(i+2)^2/4\rfloor$. Then (1) gives $q_{n,i}\le(i+1)M_i^n$ for every $i$ since $(i-b+1)^{-b}\le1$. For fixed $i$, (2) shows that $q_{n,i}/M_i^n$ converges to the sum of $(i-b+1)^{-b}$ over maximizing indices $b$. For $i=2h-2,2h-1,2h$, the respective limits are $a_h,b_h,d_h$.

The successive ratios $M_{2h-1}/M_{2h-2}$ and $M_{2h}/M_{2h-1}$ both equal $(h+1)/h$. These ratios strictly decrease between pairs. At $s=h/(h+1)$ the sequence $M_i s^i$ therefore has its maximum $D$ at exactly $i=2h-2,2h-1,2h$. Since $M_i$ grows quadratically, the coefficient and tail estimates give

$$
\frac{L_n(s^n u)}{D^n}\longrightarrow u^{2h-2}(a_h+b_hu+d_hu^2)
$$

locally uniformly. Write $b_h=X+Y$ with $X=(h+1)^{-(h-1)}$ and $Y=h^{-h}$. Then $XY/(a_hd_h)=(h+1)/h=:v_h>1$, so $b_h^2/(a_hd_h)\ge4v_h>4$. This gives two distinct negative zeros of $a_h+b_hu+d_hu^2$. The corresponding positive reciprocals of their moduli are $\kappa_h^+>\kappa_h^-$, since the substitution $u=-1/v$ gives $a_hv^2-b_hv+d_h$. Localization gives the claimed asymptotics and modulus indices after inverting the nonzero zeros of $L_n$.

In fact $\kappa_h^+/\kappa_h^->v_h$. If $K=\kappa_h^+/\kappa_h^-$, Vieta’s formulas give $K+2+K^{-1}=b_h^2/(a_hd_h)\ge4v_h>v_h+2+v_h^{-1}$. The last strict inequality holds for $v_h>1$, and $t+2+t^{-1}$ is strictly increasing for $t>1$. In decreasing modulus, the four same-scale zeros therefore occur in the order

$$
|\beta_{n+1,2h-1}|> |\beta_{n,2h-1}|>
|\beta_{n+1,2h}|>|\beta_{n,2h}|
$$

for sufficiently large $n$. Also $|\beta_{n,2h}|/|\beta_{n+1,2h+1}|\to\infty$ since $v_h>v_{h+1}$. Reversing the modulus inequalities on the negative axis gives the second interlacing statement.

## Prior work checked

The earlier endpoint estimates of Durán concern the ordinary Eulerian polynomials and use their reciprocal symmetry. In the square, the coefficient limits at the two ends differ, and the repeated growth ratios at the high-degree end require a quadratic limit. [Durán, Theorem 2](https://arxiv.org/pdf/2404.03249v2)

On 25 November 2026, targeted web and Firecrawl searches used combinations of “Eulerian matrix square,” “Mao Wang,” “Narayana transformation,” “extreme roots,” “asymptotics” and “interlacing.” The source paper, the public investigation of the ordinary square and the Omega reading note were checked directly. The public investigation documents the bivariate recurrence and counterexamples to stronger transformation and stability claims. The Omega reading note treats the Delannoy clause. These sources and targeted searches did not locate these endpoint formulas for the Eulerian square. [Mao–Wang](https://arxiv.org/abs/2607.01572) · [Public issue #83](https://github.com/1337isnot1337/solved-conjectures/issues/83) · [Pinned univariate sign approach](https://github.com/1337isnot1337/solved-conjectures/blob/0d53955/research/mao-wang/eulerian-research.md) · [Pinned transform obstruction and bivariate recurrence](https://github.com/1337isnot1337/solved-conjectures/blob/0d53955/research/mao-wang/ROOT-EULERIAN-CHECKPOINT.md) · [Omega reading note](https://the-omega-institute.github.io/trureturing-mdbook/Library/Zeros/maowang2026narayana.html)
