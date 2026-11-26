# Limits of root-order invariants for the Motzkin transfer

Research follow-up to [PR #118](https://github.com/ProgramComputer/open-math-research/pull/118) and [issue #3](https://github.com/ProgramComputer/open-math-research/issues/3). The preceding package studies a recurrence on appended word letters. The present recurrence uses a shifted variable and Motzkin tiles.

Set $u=t-1$ and let $G(x)=1+\sum_{n\ge1}C_n(1+u)x^n$. The known equation $G=1-ux^2G+x(1+ux)G^2$ becomes, for $M=(G-1)/x$,

$$
M=1+(2x+ux^2)M+x^2(1+ux)M^2.
$$

This is the excursion equation with two short level tiles, a short up tile, a short down tile, and marked long level and down tiles. Thus the polynomial of excursions of chronological length $n$ is $C_{n+1}(1+u)$. [Short-peak enumeration](https://doi.org/10.26493/2590-9770.1794.fc5) · [Shifted generating function checkpoint](https://github.com/1337isnot1337/solved-conjectures/blob/main/docs/alexandersson-catalan-peaks-research.md)

Write $F_n(h)$ for the down-long Motzkin states, with support $0\le h\le n$. Let $(U f)_h=f_{h-1}$, $(L f)_h=f_{h+1}$ and $f_{-1}=0$ at the height boundary. Then $LU=I$ and
$$
A=2I+U+L=(I+L)(I+U),\qquad B=I+L,\qquad
F_n=A F_{n-1}+uB F_{n-2}.
$$
Writing $W_n=(I+U)F_n+uF_{n-1}$ gives the pending-state factorization $F_{n+1}=B W_n$. These identities follow from half-line shift multiplication. The endpoint is the shifted strict Catalan peak polynomial. The examples below concern the scope of possible abstract inductions, rather than the real-rootedness or interlacing of the actual endpoint family.

## Pairwise root order alone does not propagate

The genuine latest rows at times three and two, respectively, are
$$
f=(14+5u,14+2u,6,1),\qquad p=(5+u,4,1).
$$
Multiply $f_1$ by $50$ and $p_0$ by $20$, leaving the other states. All input degrees and roots, and hence every weak or strict pairwise proper-position relation, remain unchanged. This holds also after multiplying any states by $u$. However the next height-zero output is
$$
2f_0+f_1+u(p_0+p_1)=728+214u+20u^2,
$$
with discriminant $-12444$. An abstract invariant consisting only of pairwise root-order comparisons across the two chronological input layers therefore cannot imply that the next endpoint is real-rooted.

## Pending state factorizations add constraints but still allow a failure

The genuine pending inputs are
$$
w=(5+3u,9+2u,5,1),\qquad z=(2+u,3,1),
$$
with $f=Bw$ and $p=Bz$. Replace only $w_2=5$ by $100$, preserve $p,z$, and set the new $f=Bw$. This gives $f=(14+5u,109+2u,101,1)$. All states in the four layers still have nonnegative coefficients. The only nonzero root among any of these states that moved is the unique leftmost one, formerly the $f_1$ root $-7$ and now $-109/2$. All other roots lie strictly to its right, so all pairwise interlacing and ordering comparisons remain as before, including comparisons after multiplying any state by powers of $u$. Both pending factorizations remain exact. The next endpoint becomes
$$
137+21u+u^2,
$$
with discriminant $-107$. This perturbation does not retain the separate identity that generated the changed $w$ from the previous chronology.

One can alternatively retain the exact latest update $w=(I+U)p+uF_1$, $f=Bw$ with the genuine $F_1=(2,1)$. Change just $p_2=1$ to $100$ and update $w,f$ by those identities. Again the only nonzero root that changes is the leftmost $f_1$ root. The next endpoint is $141+21u+u^2$, with discriminant $-123$. This perturbation instead loses the nonnegative backward factorization $p=Bz$, since $z_2=p_2$ and $z_1=p_1-p_2<0$.

## Joint consistency is a substantive extra condition

The examples above do not rule out using both conditions together. Indeed at exactly these small degrees they force the next endpoint to be real-rooted. Write the earlier row as $(a,b)$ and the middle row as $(c+xu,d,e)$ with all parameters nonnegative, and assume that the middle row admits a nonnegative backward factorization $p=Bz$. Then $e\le d$. If the latest update is exact, the next endpoint is
$$
(5c+4d+e)+(5x+2a+3b+c+d)u+xu^2.
$$
Its discriminant is at least $(5x+c+d)^2-20x(c+d)=(5x-c-d)^2$. Thus any successful invariant must use more than root comparisons and one of the two consistency constraints alone, and the small-degree calculation does not establish the needed all-degree consequence.

The [standard-library replay](check.py) reconstructs the actual input layers, checks the two factorizations, compares nonzero root order by exact fractions and checks all three negative discriminants. An [independent tile enumeration](independent-tiles.py) checks the genuine layers and supplies a separate arithmetic reconstruction. [Review and scope](review.md)

**⬜ None** for this proof-method obstruction. The [all-length theorem](../README.md) concerns the actual Catalan peak polynomials and is already proved.

~~~sh
python3 -B topics/catalan-word-peaks/motzkin-pending/check.py
python3 -B topics/catalan-word-peaks/motzkin-pending/independent-tiles.py
~~~
