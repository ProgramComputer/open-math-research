# Positive interlacing weights and the insertion residue

For fixed $k$, write $P_n=E_{n,k}/t$. Suppose $p=P_n$ and $q=P_{n-1}$ are monic, strictly interlacing, with simple negative roots. Put
$$
\ell=L/t=\binom{n}{k-1}A_{k-1}P_{n+1-k},
\qquad
\mu_i=\frac{\ell(x_i)}{(1-x_i)p'(x_i)}
$$
at the roots $x_i$ of $p$, for a nonzero lag. The quotient has positive weights
$$
\frac{q(t)}{p(t)}=\sum_i\frac{w_i}{t-x_i},\qquad
w_i=\frac{q(x_i)}{p'(x_i)}>0,\qquad \sum_i w_i=1.
$$
The results below isolate what these weights can control. The insertion inequality for the actual general rows remains open. [Insertion recurrence](insertion-lag.md) · [Exact residue trace](residue-traces.md)

## Bare interlacing cannot bound the residue

Set $R_s(t)=1+st+t^2$. Take the genuine $k=3$ rows
$$
P_3=1+t,\qquad P_4=R_4,\qquad P_5=(1+t)R_{10},
$$
then use the synthetic old row $p_\delta=P_6=R_{10-\delta}R_{10+\delta}$ for $0<\delta\le1$. The smaller root modulus of $R_s$ strictly decreases with $s>2$, and the other modulus is its reciprocal. This proves strict interlacing at every consecutive pair in this chain. Every row is monic and reciprocal with positive coefficients, and at $\delta=1$ the coefficients are integers.

Retain the true formula for the next lag, $\ell=15(1+t)R_4$. At the root $x\in(-1,0)$ of $R_{10+\delta}$, the two ratios are
$$
w(x)=\frac{1+x}{2(2x+10+\delta)},\qquad
\mu(x)=\frac{15(6+\delta)(1+x)}{2\delta(1-x)(2x+10+\delta)}.
$$
Indeed $R_{10-\delta}(x)=-2\delta x$, $R_{10}(x)=-\delta x$ and $R_4(x)=-(6+\delta)x$. At either root of either factor of $p_\delta$, the same formula for $w$ with that factor's $s$ holds. All four weights have positive finite limits as $\delta\to0$, while $|\mu(x)|$ is unbounded. For the integer example $\delta=1$ the exact bracket $-92/1000<x<-91/1000$ gives $\mu(x)>4$ by substitution in the preceding formula. The signed sum of the residues in this family remains bounded. In fact $\ell/((1-t)p_\delta)$ is $O(t^{-2})$, so summing residues at the negative roots and at 1 gives $\sum_i\mu_i=\ell(1)/p_\delta(1)=180/(144-\delta^2)$.

The chain uses the genuine rows through $P_5$ and a synthetic $P_6$ in place of the row given by the insertion recurrence. The example refutes an implication from earlier interlacing, reciprocal positivity and the shape of the new lag alone. A sufficient condition needs a property of the actual step that constructs $P_n$, or another way to distinguish it from the synthetic row.

## The canonical compression gives a quantitative bound for one component

The positive weights determine the monic Euclidean predecessor $r_*$ by
$$
p=(t-a)q-b r_*,
\qquad a=\sum_iw_i x_i,\qquad b=\sum_iw_i(x_i-a)^2>0.
$$
Indeed expanding $p/q$ at infinity yields these $a,b$ and the monic remainder $r_*$ of degree $\deg p-2$. The quotient $r_*/q$ has positive weights at the roots of $q$, since $r_*(y)=-p(y)/b$ there. This is the trailing principal compression determined by the pair $p,q$ alone.

For $k=3$ the actual residual is $r=P_{n-2}$. Set $\Delta=r-r_*$. At every root $x_i$ of $p$ the exact decomposition is
$$
\mu_i=\binom n2\frac{1+x_i}{1-x_i}
       \left(\frac{(x_i-a)w_i}{b}+\frac{\Delta(x_i)}{p'(x_i)}\right).
$$
Using $\sum w_i(x_i-a)=0$ and Cauchy–Schwarz on the other atoms gives
$$
w_i|x_i-a|\le\sqrt{b\,w_i(1-w_i)}\le\frac{\sqrt b}{2}.
$$
Write $c_n=[t^2]E_{n,k}$ and $e_n=[t^3]E_{n,k}$. Reciprocity and the first three terms of $q/p$ at infinity give
$$
b=e_{n-1}-e_n+c_{n-1}(c_n-c_{n-1}).
$$
The exact two-excedance formula gives $c_n\ge2c_{n-1}$ and $c_{n-1}\ge2^{n-2}-(n-1)$. The run encoding gives $e_n\le3^n$. Hence $b\ge(2^{n-2}-(n-1))^2-3^n>4^{n-3}$ for $n\ge14$. For the last bound use $n-1\le2^{n-4}$ and $(3/4)^n<5/256$. Since $|1+x_i|/(1-x_i)\le1$, the canonical term contributes at most
$$
\frac{\binom n2}{2\sqrt b}<\frac{2n(n-1)}{2^n}<\frac1{40}\qquad(n\ge14).
$$
Thus this approach for $k=3$ reduces to controlling the compression defect $\Delta(x_i)/p'(x_i)$. The canonical coefficient bound is independent of root separation. [Two-excedance formula and run encoding](proof.md)

## The two weight measures on genuine rows

At a root $y_j$ of $q$, write
$$
\omega_j=\frac{P_{n-2}(y_j)}{q'(y_j)},\qquad
\omega_j^*=\frac{r_*(y_j)}{q'(y_j)}
          =\frac{(-y_j)(1-y_j)}{b}(1+\mu_{n-1}(y_j)).
$$
The second equality is the actual insertion recurrence for $p$ at the preceding row's root. Both measures have positive weights summing to one for strictly interlacing actual rows. The defect has the representation
$$
\frac{\Delta(t)}{q(t)}=\sum_j\frac{\omega_j-\omega_j^*}{t-y_j}.
$$

Already for the genuine $k=3,n=6$ row $p=1+36t+86t^2+36t^3+t^4$, division gives $a=-25$, $b=200$ and $r_*=t^2+(6/5)t+3/25$. At the first pole $y=-5+2\sqrt6$ of $q=P_5$, one has $P_4(y)=-6y$ and $r_*(y)=(22/25)y^2$. The weight ratio is $-75/(11y)>60$.

For every fixed $k\ge3$, this ratio tends to infinity at the first pole as $n$ grows along the genuine strictly interlacing rows. The run-color encoding with a fixed number of colors gives $c_m\sim2^m$ and $e_m\le3^m$. At the first root $y$ of $q$, the first-rank estimate gives $y\sim-2^{-(n-1)}$. The bounds $[t^j]E_{m,k}\le j^m$ make the terms past the linear term of $P_m$ negligible at this point for every fixed row offset $n-m$. They also make the terms past the constant term of $q'$ negligible relative to $c_{n-1}$. Indeed the first tail term relative to its comparison scale is $O((3/4)^m)$, and for consecutive remaining terms the exponential part of the ratio is bounded by $(2/3)^m$ times a constant depending on the row offset. Thus
$$
P_{n-2}(y)\sim1/2,\qquad q'(y)\sim2^{n-1},\qquad b\sim4^{n-1}.
$$
The preceding insertion ratio $\mu_{n-1}(y)$ is $O(n^{k-1}2^{-n})$ by the same coefficient estimates, using $P_{n-k}(y)=O(1)$ and $A_{k-1}(y)=O(1)$. Consequently
$$
\omega_j\sim \tfrac12\,2^{-(n-1)},\qquad
\omega_j^*\sim8^{-(n-1)},\qquad
\frac{\omega_j}{\omega_j^*}\sim\tfrac12\,4^{n-1}.
$$
The asymptotic rules out an induction using $\omega_j\le C\omega_j^*$ with a fixed $C$. The identity for the signed difference suggests controlling its Cauchy transform after evaluating at the current row's nodes and multiplying by $w_i$. Total weight bounds give no such local control when $x_i$ and $y_j$ are close, as the synthetic example shows.

## Equivalent structured sign test and a combinatorial sign obstruction

Let $\mathrm{Bez}_p(u)$ have kernel $(p(t)u(s)-u(t)p(s))/(t-s)$. At the roots of $p$, evaluation diagonalizes it by Vandermonde congruence with entries $p'(x_i)u(x_i)$. Thus positivity of $\mathrm{Bez}_p(q)$ is exactly the positivity of the interlacing weights. The strict insertion bound is equivalent to the stronger pair of inequalities

$$
\mathrm{Bez}_p((1-t)p')+\mathrm{Bez}_p(\ell)\succ0,\qquad
\\,\mathrm{Bez}_p((1-t)p')-\mathrm{Bez}_p(\ell)\succ0.
$$

This makes the required signed operator comparison explicit. For noncentral roots one can also pass to the reciprocal coordinate $u=t/(1+t)^2$ used in the residue trace. With old polynomial $G(u)$ and lag numerator $H(u)$ in that coordinate, the two positive forms become $\mathrm{Bez}_G((-u(1-4u)G'\pm H)\bmod G)$. Reduction modulo $G$ keeps the arguments within degree $<\deg G$ while preserving their values at the roots.

One direct combinatorial alternative is to split the new row by the length $j$ of the cycle containing the maximum. At an old root the insertion derivative contribution equals the sum of the terms with $j>k$. Those terms can have opposite signs on a genuine row. For example at $k=3,n=7$, take the root $x\in(-1/4,-1/5)$ of the genuine reciprocal factor $1+91t+386t^2+91t^3+t^4$ in $P_7$. Its endpoint signs are $245/256$ and $-1554/625$. In the new row the $j=4$ term is $35x A_3(x)^2<0$, and the $j=5$ term is $35x(1+x)^2R_{10}(x)>0$. The inequalities follow on the whole bracket from $A_3=R_4>0$ and $R_{10}<0$. A lower bound from this decomposition has to account for cancellations between the marked lengths.

The next mathematical test for an induction based on weights is a bound on the signed compression-defect transform at the specific current nodes. A direct structured proof of the Bezoutian inequalities would also suffice. Neither follows from the positivity and unit mass of the individual measures.

## Exact reproduction

Run the following from the repository root with Python 3.10 or later.

~~~sh
python3 -I -B topics/long-cycle-excedances/verify_jacobi_defect.py
~~~

The checker enumerates admissible permutations directly for $k=3$ and $3\le n\le7$. It reconstructs the genuine rows in the examples, certifies the integer synthetic chain and its ratio greater than four by rational brackets, checks the canonical division and genuine weight ratio greater than 60, and verifies the opposite signs of the two marked lengths. The canonical contribution bound and the fixed-$k$ asymptotic use the separate written arguments above. **⬜ None.** There is no checked Lean or Rocq proof.

## Independent review

An independent agent-assisted reviewer expanded $q/p$ at infinity to reconstruct the variance identity and checked the complementary-mass Cauchy–Schwarz bound for its individual atoms. The reviewer verified the exponential coefficient estimate and the $1/40$ canonical bound for $k=3$ and $n\ge14$. At fixed $k$, the reviewer checked the geometric tails for the first root and its derivative, the preceding insertion ratio tending to zero, and the resulting asymptotic $\omega_j/\omega_j^*\sim4^{n-1}/2$. The reviewer also checked the synthetic formulas and the exact genuine example at $n=6$. The ratio greater than four concerns the synthetic chain. The unbounded comparison of the two weight measures concerns genuine rows.
