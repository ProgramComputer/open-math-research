# Excedance zeros for permutations with long cycles

Let $E_{n,k}(t)$ count permutations of $n$ letters by excedances, with every cycle of length at least $k$. At $k=3$, the polynomial $E_{n,k}(t)/t$ has $n-2$ simple negative zeros at every $n\ge3$, and they strictly interlace the zeros in the next row. Both conclusions also hold for every $k\ge3$ when $n\ge Bk^2$ for one absolute constant $B$. The zero at the origin is simple. Alexandersson's full conjecture still asks for the remaining sizes at $k\ge4$. [Original statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Sources and prior work](LITERATURE.md)

The [proof at minimum length three](fixed-threshold.md) compares consecutive rows through their generating function. A [decreasing-run count](small-ranks.md) determines the signs at roots near zero. The [uniform estimate](quadratic-cutoff.md) bounds the dependence on $k$. At $k=3$ the estimates apply from row 400. The proof of existence of the general constant $B$ gives no numerical value. [Manuscript](paper.tex)

**Formal verification · ⬜ None.** An independent research agent reviewed the proof and recorded the finite and uniform checks in two reports. The exact finite certificate covers rows 3 through 401, 398 consecutive pairs and 39,800 dyadic brackets. Inclusion-exclusion reproduces every coefficient vector. Direct enumeration reproduces rows 3 through 8, and clearing denominators verifies all 79,600 endpoint signs. [Certificate](threshold-three-prefix.jsonl.gz) · [Analytic and computational review](review-fixed-threshold.md) · [Review of the uniform bound](review-quadratic-cutoff.md)

From the repository root, use Python 3.10 or later.

~~~sh
python3 -I -O topics/long-cycle-excedances/verify_threshold_three.py
python3 -I -O topics/long-cycle-excedances/verify_cycle_deletions.py
python3 -I topics/long-cycle-excedances/verify_endpoints.py topics/long-cycle-excedances/threshold-three-prefix.jsonl.gz
~~~
