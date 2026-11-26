# Sharp insertion bound at the central root

Let $E_{n,k}(t)$ count permutations of $[n]$ with minimum cycle length at least $k$, by excedances, and put $P_n=E_{n,k}/t$ when $n\ge k\ge3$. At a root $x$ of $P_n$, insertion of the new maximum gives
$$
P_{n+1}(x)=D(x)+L(x),\qquad
D(t)=t(1-t)P_n'(t),\qquad
L(t)=\binom n{k-1}A_{k-1}(t)E_{n+1-k,k}(t),
$$
where $A_j$ is the ordinary Eulerian polynomial. Set $E_{0,k}=1$ and $E_{j,k}=0$ for $0<j<k$. [Recurrence and original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances)

**Theorem.** Every odd row has a simple root at $-1$. For odd $k$ the ratio $\mu(-1)=L(-1)/D(-1)$ vanishes. For each even $k=2v\ge4$, its maximum over all eligible odd $n$ occurs uniquely at $n=2k-1$ and equals
$$
\frac{\lambda_v^2}{v\lambda_{2v}},\qquad
\lambda_j=\sum_{p=1,3,5,\ldots}p^{-2j}.
$$
Across all $n,k$ having a central root, $0\le\mu(-1)\le35/68$. Equality in the upper bound occurs exactly at $(n,k)=(7,4)$. Every eligible even row is nonzero at $-1$.

## Signed cycle counts

An $l$-cycle has polynomial $tA_{l-1}(t)$. If $l$ is odd and $l\ge3$ this vanishes at $-1$ by reciprocity. For $l=2j$, the Eulerian pole formula at $-1$ gives the signed weight, divided by $(2j)!$,
$$
\frac{-A_{2j-1}(-1)}{(2j)!}
=\left(\frac{-4}{\pi^2}\right)^j\frac{\lambda_j}{j}.
$$
Indeed the sum over odd poles $ip\pi$ in the coefficient of order $2j-1$ equals $2(-1)^j\pi^{-2j}\lambda_j$. [Derivation of the pole formula, equation (5)](first-lag.md)

Write $a=-4/\pi^2$, $v=\lceil k/2\rceil$, and
$$
d_m=[z^m]\exp\left(\sum_{j\ge v}\frac{\lambda_j}{j}z^j\right).
$$
The labeled set of cycles gives $E_{2N,k}(-1)=(2N)!a^N d_N$. Here $d_0=1$, $d_m=0$ for $0<m<v$, and $d_m\ge\lambda_m/m>0$ for $m\ge v$. In particular every eligible even row is nonzero there. Any odd row vanishes there since each permutation of odd size has at least one odd cycle. Differentiating the series gives
$$
m d_m=\sum_{j=v}^m\lambda_jd_{m-j}.
$$

Write the old size as $n=2N-1$. For odd $k$, $A_{k-1}(-1)=0$ and $N\ge v$. The insertion equation gives $D(-1)=-E_{2N,k}(-1)\ne0$, so the root is simple and the lag vanishes. For even $k=2v$, eligibility gives $N\ge v+1$. Evaluating the binomial factor and its two cycle polynomials gives
$$
L(-1)=-2(2N-1)!a^N\lambda_v d_{N-v}.
$$
Since $P_{n+1}(-1)=-E_{2N,k}(-1)$, subtraction and the recurrence for $d_N$ give
$$
D(-1)=-2(2N-1)!a^N\sum_{j=v+1}^N\lambda_jd_{N-j}.
$$
The sum contains the positive term $\lambda_N$. This proves simplicity and yields the nonnegative ratio
$$
\mu(-1)=\frac{\lambda_v d_{N-v}}{\sum_{j=v+1}^N\lambda_jd_{N-j}}.
$$

## Locating the maximum

Put $c=\lambda_v$. We have $c\le25/24$, since $\sum_{p\ge3}p^{-4}\le\int_2^\infty u^{-4}du$. For $v\ge2$ the tail of all weights satisfies
$$
\delta=\sum_{j\ge v}(\lambda_j-1)
\le\frac98\sum_{p\ge3}p^{-4}
\le\frac98\left(3^{-4}+\int_3^\infty u^{-4}du\right)=\frac1{36}.
$$
The first inequality uses $1/(1-p^{-2})\le9/8$ for $p\ge3$.

We claim $d_m\le C:=c/(v+1/2)$ for every $m>v$. For $v<m<2v$ there is only one possible summand and $d_m=\lambda_m/m\le C$. For $m\ge2v$, separate $d_0$ and $d_v=c/v$ in the recurrence. The $m-2v$ remaining potentially nonzero summands involve indices of $d$ greater than $v$. Induction gives
$$
m d_m\le c+c^2/v+C(m-2v+\delta)\le mC.
$$
The last inequality follows from $1/2+c(1+1/(2v))+\delta<2\le v$.

If $N-v=v$, then the numerator of the ratio is $c^2/v$ and its denominator is $\lambda_{2v}$. If $0<N-v<v$, its numerator vanishes. In every remaining case its denominator is at least $\lambda_N\ge1$, so the ratio is at most $c^2/(v+1/2)$. This is strictly smaller than $c^2/(v\lambda_{2v})$ because
$$
\lambda_{2v}-1\le\int_2^\infty u^{-4v}du=\frac{2^{1-4v}}{4v-1}<\frac1{2v}.
$$
This proves uniqueness at $N=2v$, which is $n=2k-1$.

For $v\ge3$ the maximum is at most $(25/24)^2/3<35/68$. At $v=2$, $n=7$, the old polynomial is $A_6$ with $A_6'(-1)=136$. The lag at $-1$ is $-35A_3(-1)^2=-140$, giving $\mu(-1)=140/272=35/68$.

The central root now satisfies the insertion inequality throughout the conjecture’s range. The noncentral reciprocal pairs remain. [Exact test for those pairs](residue-traces.md)

**⬜ None.** The theorem has a written proof. An independent agent-assisted check rederived the signed cycle recurrence and tested every eligible odd row through size 80, including 1,521 parameter pairs. The independent review also checked the strict comparison for every $m>v$ that gives uniqueness at $n=2k-1$. [Exact coefficient replay](verify_central_insertion.py)

~~~sh
python3 -I -O topics/long-cycle-excedances/verify_central_insertion.py
~~~
