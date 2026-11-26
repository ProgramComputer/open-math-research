# Excedance zeros for permutations with long cycles

There is a single $N$ such that for every $n\ge N$ and every $3\le k\le n$, the nonzero roots of $E_{n,k}$ are simple, negative and strictly interlace the nonzero roots in the next row at the same $k$. Here $E_{n,k}$ enumerates permutations of $n$ letters by excedances with minimum cycle length at least $k$. The result reduces Alexandersson’s two-parameter conjecture to finitely many pairs. The proof gives no numerical $N$, so the finite set has yet to be certified. [Uniform proof](uniform-interlacing.md) · [Independent review](review-uniform-interlacing.md)

At $k=3$, the polynomial $E_{n,k}(t)/t$ has $n-2$ simple negative zeros at every $n\ge3$, and they strictly interlace the zeros in the next row. Both conclusions also hold for every $k\ge3$ when $n\ge Bk^2$ for one absolute constant $B$. The zero at the origin is simple. The remaining cases have $k\ge4$ and $n<N$. [Original statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Sources and prior work](LITERATURE.md)

The [proof at minimum length three](fixed-threshold.md) compares consecutive rows through their generating function. A [decreasing-run count](small-ranks.md) determines the signs at roots near zero. The [uniform estimate](quadratic-cutoff.md) bounds the dependence on $k$. At $k=3$ the estimates apply from row 400. The proof of existence of the general constant $B$ gives no numerical value. [Manuscript, including the uniform theorem](paper.tex)

**Formal verification · ⬜ None.** An independent research agent reviewed the proof and recorded the finite and uniform checks in two reports. The exact finite certificate covers rows 3 through 401, 398 consecutive pairs and 39,800 dyadic brackets. Inclusion-exclusion reproduces every coefficient vector. Direct enumeration reproduces rows 3 through 8, and clearing denominators verifies all 79,600 endpoint signs. [Certificate](threshold-three-prefix.jsonl.gz) · [Analytic and computational review](review-fixed-threshold.md) · [Review of the uniform bound](review-quadratic-cutoff.md)

For every $k\ge3$, strict interlacing holds from size $2k-1$ to $2k$, the first transition in which an admissible second cycle appears. Both signs of its contribution preserve the alternating signs at the old roots. An independent check reconstructed all 118,206 endpoint signs in the finite part of the proof. [Boundary theorem](first-lag.md) · [Independent review and replay](review-first-lag.md)

At the central root $-1$, the insertion term divided by the derivative term is at most $35/68$ in every eligible odd row, with equality only at $(n,k)=(7,4)$. An exact sum of squares test for the remaining reciprocal root pairs succeeds in all 441 previously certified transitions with nonzero insertion term. The all-size question for those noncentral roots remains open. [Sharp central-root theorem](central-insertion.md) · [Two exact trace methods](residue-traces.md) · [Insertion recurrence](insertion-lag.md)

Run the threshold-three checks from the repository root with Python 3.10 or later.

~~~sh
python3 -I -O topics/long-cycle-excedances/verify_threshold_three.py
python3 -I -O topics/long-cycle-excedances/verify_cycle_deletions.py
python3 -I topics/long-cycle-excedances/verify_endpoints.py topics/long-cycle-excedances/threshold-three-prefix.jsonl.gz
~~~
