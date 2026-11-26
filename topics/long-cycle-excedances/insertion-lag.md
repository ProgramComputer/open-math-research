# A finite test of the insertion recurrence at the old roots

Put $P_n(t)=E_{n,k}(t)/t$ for $n\ge k\ge3$ and let $x$ be a negative simple root of $P_n$. In the next row the derivative and the new $k$-cycle contribute
$$
 P_{n+1}(x)=(1-x)xP_n'(x)+L(x),\qquad
 L(t)=\binom{n}{k-1}A_{k-1}(t)E_{n+1-k,k}(t).
$$
An all-size estimate $|L(x)|<|(1-x)xP_n'(x)|$ would give strict interlacing by induction. The single-cycle initial row is $P_k=A_{k-1}$, and the Eulerian recurrence proves the base real-rootedness. The inequality forces alternating next-row signs at every old root; the positive leading and constant coefficients supply the two outer signs. The uniform large-row theorem leaves a finite set of unknown size. This induction is an alternative way to close it. [Original recurrence](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)

To test the inequality we construct the two new polynomials with $+L$ and $-L$ from identical old rows. Multiplication of $L$ by $-1$ affects only the new test polynomial, and every subsequent old polynomial uses the original positive recurrence. Both test polynomials have degree one greater than the old row and have constant and leading coefficients one. A signed Euclidean chain for either pair has positive leading coefficients and degree drops exactly one at every step until a nonzero constant. The relation $p=Aq-c r$ for $c>0$ gives opposite signs of $p$ and $r$ at each root of $q$, so induction back up the chain proves the directed alternation. At each old root the two new values have the same sign as $(1-x)xP'_n(x)$. This is equivalent to the strict absolute inequality above.

Exact computation covered every $3\le k\le n\le46$ (990 rows). It checked both new-cycle signs in all 946 consecutive pairs ending by size 46. In 441 of those pairs the new-cycle term was nonzero. The archive stores each original coefficient vector and the two chain degree lists, allowing the entire calculation to be replayed. This verifies the induction inequality on a finite range. [Data](insertion-lag.jsonl.gz) · [Checker](verify_insertion_lag.py)

A factor of two in front of the absolute left-hand side would already fail at $(n,k)=(5,3)$. The old polynomial is $(1+t)(1+10t+t^2)$ and $L=10t(1+t)^2$. At either root of the quadratic, reduction by $t^2+10t+1=0$ gives $L/((1-t)tP'_5)=5/6$.

~~~sh
python3 -I -O topics/long-cycle-excedances/verify_insertion_lag.py
~~~
