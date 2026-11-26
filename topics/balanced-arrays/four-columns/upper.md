# Explicit upper phase estimates for four balanced columns

Let $P_n(q)$ count the unweighted four-column balanced binary arrays with row cap two. Use $q=-t^4$, $t>0$, and put
$$
\zeta=e^{i\pi/4},\qquad S(t)=1+4\zeta t+6it^2,\qquad
\Lambda(t)=\frac{2\zeta t+4it^2}{S(t)},\qquad
\Psi_n(t)=n\arg S(t)-\frac32\arg\Lambda(t).
$$
The argument of $S$ is in $(0,\pi/2)$. Below all other arguments are principal. This note proves the following sign estimate with explicit cutoff:

$$
n\ge200,\quad t\ge\frac{38}{7},\quad
\Psi_n(t)=j\pi,\quad 0\le j\le\lfloor n/2\rfloor-1
\quad\Longrightarrow\quad
\\,\mathrm{sgn}\\,P_n(-t^4)=(-1)^j.
$$

The sign at the far endpoint is $(-1)^{\lfloor n/2\rfloor}$ from the leading term. The top quota is attained by taking $\lfloor n/2\rfloor$ rows of each of the two types $1100$ and $0011$. The finite-node condition includes every other needed upper sign node.

## Exact four saddle values from opposite-pair coordinates

Integrate $R(t,y)^n=(1+t e_1(y)+t^2 e_2(y))^n$ on the normalized torus $\prod_{a=1}^4 y_a=-1$. This is exactly $P_n(-t^4)$. For $\theta=(\theta_1,\theta_2,\theta_3)\in[-\pi,\pi]^3$, the two lifts of the comparison coordinates $y_1y_{a+1}/i=e^{i\theta_a}$ are
$$
y_a=\epsilon\zeta \exp(i\epsilon_a\cdot\theta/2),\qquad \epsilon\in\{1,-1\},
$$
where $\epsilon_1=(1,1,1)$ and the other three vectors have exactly two negative entries. Averaging over $\epsilon$ kills monomials of odd total degree. At even total degree the angular exponents are integers. Their simultaneous vanishing forces all four original exponents to be equal. The angular average on the two lifts is therefore the intended torus integration.

Write
$$
A=\tfrac13\sum_{a=1}^3\cos\theta_a,\qquad
C=\prod_{a=1}^3\cos(\theta_a/2),\qquad
D=\prod_{a=1}^3\sin(\theta_a/2).
$$
The exact pair sum is $e_2(y)=6iA$, and the singleton sum is $4\epsilon\zeta(C-iD)$. Set $v=1/t$, $h=(2/3)e^{-i\pi/4}v$, $d=-iv^2/6$, and $c=\sqrt2/3$, so $h=cv(1-i)$. On the lifts,
$$
Z_\epsilon:=\frac{R(t,y)}{6it^2}=A+\epsilon h(C-iD)+d,
\qquad L_\epsilon=1+\epsilon h+d.
$$
At $A=1$ the two values are $L_+$ and $L_-$. Torus conjugation sends $A$ to $-A$ and $R$ to its conjugate, preserving measure. The zero set of $A$ has measure zero, since with two angles fixed the third angle must solve one cosine equation. Thus integrating the $A\ge0$ half and taking twice its real part retains all four saddle values. In particular, the conjugates of $6it^2L_\pm$ are accounted for with their exact phases.

## A bound relative to a common positive integral

Let $d\mu=d\theta/(2\pi)^3$. On $A\ge0$ set $\delta=1-A\in[0,1]$ and
$$
M_n=\int_{A\ge0} A^n\,d\mu .
$$
Since $\sum \sin^2(\theta_a/2)=3\delta/2$, the half-angle products obey
$$
1-3\delta/2\le C\le 1-\delta/2,qquad |D|\le(\delta/2)^{3/2}.
$$
For the lower bound use $\sqrt{1-u}\ge 1-u$ and $\prod(1-u_a)\ge1-\sum u_a$. The cosine factors are nonnegative in the selected angular cube. For the upper bounds use arithmetic-geometric means on the squared cosines and squared sines. Consequently
$$
|C-iD-A|\le \sqrt{3/8}\,\delta\le\frac58\delta .
$$
Subtracting the constant saddle value times $A$ gives
$$
|Z_\epsilon-L_\epsilon A|
\le\left(\frac{5v}{12}+\frac{v^2}{6}\right)\delta .
$$
For $0<v\le 7/38$, one has $|L_\epsilon|\ge\Re L_\epsilon\ge1-cv>9/10$. Hence the last bound is at most $\eta|L_\epsilon|\delta$, where
$$
\eta=\frac{5v/12+v^2/6}{9/10}<3/32 .
$$
The difference-of-powers identity gives
$$
|Z_\epsilon^n-L_\epsilon^nA^n|
\le n\eta|L_\epsilon|^n\delta(A+\eta\delta)^{n-1}.
$$

The following explicit integral comparison holds for $n\ge200$ and $0\le\eta\le3/32$:
$$
\frac{n\int_{A\ge0}\delta(A+\eta\delta)^{n-1}\,d\mu}{M_n}<\frac52 .
\tag{1}
$$
To prove it, set $w_a=\sin(\theta_a/2)$, so $\delta=(2/3)|w|^2$. The Jacobian relative to $dw/\pi^3$ is $\prod_a(1-w_a^2)^{-1/2}$. On $\delta\le1/6$ it lies between 1 and $2/\sqrt3<7/6$ by $\prod(1-w_a^2)\ge1-|w|^2$. In radial coordinates the Jacobian-free measure is $K\delta^{1/2}\,d\delta$ with $K=2(3/2)^{3/2}/\pi^2>1/4$. The entire radial ball for $\delta\le1/6$ is inside the $w$ cube. For $B_n=\mathrm B(3/2,n+1)$ one has
$$
M_n\ge K\big(B_n-(5/6)^n\big),\qquad B_n\ge\frac1{3(2n)^{3/2}}.
$$
The second inequality integrates only $0\le\delta\le1/(2n)$, where $(1-\delta)^n\ge1/2$ by Bernoulli's inequality. The discarded beta tail has relative size at most $12n^2(5/6)^n<1/100$ for $n\ge200$.

On the smaller radial ball substitute $z=(1-\eta)\delta$ in the numerator of (1) and enlarge its range to $[0,1]$. Integration by parts gives $n\mathrm B(5/2,n)=\frac32 B_n$. After division by the lower bound on $M_n$, the contribution to (1) is at most
$$
\frac{100}{99}\frac32\frac76(32/29)^3.
$$
On the complement in $A\ge0$ one has $A+\eta\delta\le163/192$, so its contribution is at most $52n^3(163/192)^{n-1}<1/100$. Both bounds on the exponentially small expressions follow by monotonicity for $n\ge200$ and their rational comparisons at $n=200$. Adding the pieces gives (1). All numerical comparisons are recorded in [upper_constants.py](code/upper_constants.py).

For $n\ge200$ define the positive normalization
$$
N_n(t)=(6t^2)^n M_n |L_+|^n,\qquad
r_n(t)=\big|L_-/L_+\big|^n.
$$
One has $S(t)=6it^2L_+$. Taking twice the real part of the positive-half integral, with the two lifts each of weight $1/2$, now gives
$$
\left|\frac{P_n(-t^4)}{N_n(t)}-\cos(n\arg S)\right|
\le r_n(t)+(1+r_n(t))\frac52\eta.
\tag{2}
$$
The secondary phase is bounded here by its full modulus. Its contribution has thus been retained in the error with an exact modulus bound, rather than discarded in taking the endpoint limit.

## Comparison with the central phase

Put $\alpha=\pi/2-\arg S=\arctan((cv+v^2/6)/(1+cv))>0$. Since $1/3<c<1/2$, direct comparison of the arctangent argument with $v/2$ yields $\alpha<v/2$. At positive $t$,
$$
\Lambda=\frac23\frac{1+(v/2)e^{-i\pi/4}}{L_+}.
$$
The negative argument of the numerator has absolute value smaller than $\alpha$, because $c>1/(2\sqrt2)$ and the ratio $x/(1+x)$ increases with $x$. Consequently $0<\arg\Lambda<\alpha$ and $0<(3/2)\arg\Lambda<21/152$ in the upper range.

Next,
$$
|L_+|^2-|L_-|^2=4cv(1+v^2/6),\qquad
|L_+|^2\le(1+v/2)^2+(v/2+v^2/6)^2<121/100.
$$
Using $c>7/15$ and $\log(1-z)\le-z$ yields $r_n(t)\le\exp(-3nv/4)$. At a node $\Psi_n=j\pi$ with $j\le\lfloor n/2\rfloor-1$, put $x_n=n\alpha$. Then $x_n\ge\pi-21/152>29/10$ and $nv>2x_n$. Hence $r_n<1/32$. The signed main cosine at the node is $\cos((3/2)\arg\Lambda)>99/100$. But the right side of (2) is at most $1/32+(1+1/32)/4<99/100$. This proves the upper sign statement.
