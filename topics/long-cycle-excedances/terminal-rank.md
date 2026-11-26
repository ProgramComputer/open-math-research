# An obstruction to induction on the image of the largest letter

Let $E_{n,k}(t)$ enumerate permutations of $[n]$ with every cycle of length at least $k$, by excedance number. In this note $k\ge3$. Write $R_{n,j}(t)$ for the same sum restricted to $\pi(n)=n-j$, where $1\le j<n$. Thus $E_{n,k}=\sum_j R_{n,j}$. An induction comparing each summand with $E_{n-1,k}$ would imply more than Alexandersson asks. Even its first summand violates the required root order at every $n\ge2k$. Pairing the two extreme summands still fails at every $n=2k$ with $k\ge4$. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances)

## The extreme rank

For the Eulerian descent polynomial $A_m$ of permutations of $[m]$, the equalities are

$$
R_{n,1}=E_{n-1,k}+\binom{n-2}{k-2}tA_{k-2} E_{n-k,k},
\qquad
R_{n,n-1}=tR_{n,1}
$$

when $n\ge2k$. To see the first, contract the arrow $n\to n-1$. If its cycle has size greater than $k$, the contraction is a bijection onto the old permutations. Reinserting $n$ before $n-1$ replaces one excedance by one excedance. If its cycle has size exactly $k$, choose its $k-2$ other labels. In cycle notation it starts $n,n-1$, followed by an arbitrary ordering of these labels. The closing arrow contributes one rise. Internal rises have polynomial $A_{k-2}$, by complementing the ranks of the labels. The remaining cycles contribute $E_{n-k,k}$.

Inverting permutations interchanges excedances and deficiencies, so $E_{s,k}(t)=t^s E_{s,k}(1/t)$ whenever $s\ge k$. The Eulerian symmetry follows by reversing each word. Both terms in $R_{n,1}$ therefore satisfy reciprocity with exponent $n-1$. To recover the opposite rank, conjugate by the map fixing $n$ and reversing $[n-1]$. Edges within $[n-1]$ reverse their comparisons. Of the two edges incident with $n$, exactly one is a rise before and after conjugation. Consequently the exponent changes from $a$ to $n-a$, and the image of $n$ changes from $n-1$ to $1$. This proves the second identity.

Set $F=R_{n,1}/E_{n-1,k}$. It satisfies $F(t)=F(1/t)$. It is nonconstant because $F(0)=1$ after cancellation and $F(1)>1$. The extra term has order two at zero whereas the old row has order one. Differentiation gives $F'(t)=-t^{-2}F'(1/t)$. The derivative therefore has both signs on the positive axis. For weakly alternating real roots, after common factors are removed the poles of the ratio are simple and the residues all have the same sign. For equal degrees the polynomial part is constant, so its derivative has constant weak sign. This excludes both orientations of weak interlacing between the extreme summand and the old row.

## Pairing the extreme ranks

At $n=2k$ put $m=k-1$. After cancelling a common factor $t$, the ratio of the two extreme summands combined to the old row is

$$
\frac{R_{2k,1}+R_{2k,2k-1}}{E_{2k-1,k}}
  =(1+t)\left(1+\binom{2m}{m-1}\frac{t A_m(t) A_{m-1}(t)}{A_{2m}(t)}\right).
$$

The single-cycle enumerator on $s$ letters is $tA_{s-1}$, by starting its cycle with its largest letter. For $m\ge6$ the denominator has at least two roots in $(-2^{-m},0)$ while both numerator Eulerian factors are positive throughout that interval.

Here are elementary bounds proving those assertions. The Eulerian identity, obtained by applying $z\,d/dz$ successively to the geometric series, gives

$$
\frac{A_d(-z)}{(1+z)^{d+1}}=\sum_{h\ge1}(-1)^{h-1}h^d z^{h-1}
\qquad (0<z<1).
$$

For $d\le m$ and $z\le 2^{-m}$ the term magnitudes decrease, strictly from the second term onward. Grouping consecutive pairs proves strict positivity. For $d=2m$ at $z=2/4^m$, the sum of the first three terms is $-1+4(9/16)^m<0$, and the remaining alternating tail starts negative and decreases in magnitude. At $z=2^{-m}$ the sum of the first four terms is $1-2\cdot2^m+(9/4)^m>0$ because $(9/8)^6>2$. The remaining tail starts positive and decreases in magnitude. Together with $A_{2m}(0)=1$ these signs give the two roots.

Eulerian roots are simple and negative. This follows by induction from $A_{d+1}=(1+dt)A_d+t(1-t)A_d'$, testing each old root and the endpoints. The two roots of $A_{2m}$ closest to zero thus lie in the interval above. The numerator of the rational correction, including $1+t$, is strictly negative at both. The derivatives of the denominator have opposite signs there, so the residues have opposite signs. This excludes interlacing.

For $m=3,4,5$, let $p=A_{2m}$ and $q=(1+t)(p+\binom{2m}{m-1}tA_m A_{m-1})$. The following exact values give the smaller cases. In every case $q/p$ has positive slope at infinity, so a negative value of $q'p-qp'$ excludes interlacing.

| $m$ | Argument | $q'p-qp'$ |
|---:|---:|---:|
| 3 | $-4$ | $-2367000$ |
| 4 | $-1/8$ | $-109219277995695/4398046511104$ |
| 5 | $-5/2$ | $-878212034554338351/262144$ |

The obstruction holds for actual permutations with the original unit cycle weight. At these same boundary sizes the full sums satisfy strict consecutive interlacing by the reviewed two-cycle theorem. A proof by refinement would need a comparison that retains contributions from the interior ranks. [Two-cycle theorem](two-cycle-band.md) · [Independent counting and exact sign checker](verify_terminal_rank.py)

[Independent agent-assisted review](review-terminal-rank.md)

**Formal verification** ⬜ None.
