# Excedance zeros for permutations with long cycles

For every $n\ge4{,}062{,}720$ and $3\le k\le n$, the nonzero roots of the minimum-cycle-length excedance polynomial are simple, negative and strictly interlace those of the next row at the same $k$. Together with the three-cycle and threshold-three theorems, this leaves $k\ge4$ and $4k\le n<4{,}062{,}720$ as necessary conditions for a counterexample. The proof gives stronger bounds at individual ratios $n/k$. [Uniform proof and interval table](adaptive-poles/README.md) · [Manuscript](paper.pdf)

The proof uses three estimates. A signed sum over the poles handles $k\ge2000\sqrt n$, a common coefficient contour handles smaller thresholds, and exact rational bounds overlap the two ranges at moderate sizes. The checks and independent agent-assisted reviews are linked with each argument. Formal verification of this result is ⬜ None. [Signed-pole argument](uniform-hilbert/README.md) · [Wider-circle proof and audit](radial-taylor.md) · [Small thresholds](small-threshold-circle.md)

For every $k\ge3$ and $k\le n\le4k-1$, the nonzero roots of the consecutive rows are simple, negative and strictly interlace. This includes the first transition permitting four cycles. [Complete three-cycle range, proof and verification](three-cycle-complete.md) · [Manuscript](paper.pdf)

The first explicit cutoff for all thresholds was $10^{20}$. Its phase-crossing proof supplies the root count used in the sharper criterion. [Proof](effective-uniform.md) · [Independent review](review-uniform-effective.md) · [Manuscript](paper.tex)

Two estimates also apply below the uniform cutoff. For $n\ge10^6$, the contour argument applies whenever $n/(200k)>30\log n+20$. For $n\ge10{,}000$, strict interlacing holds when $k\ge2000\sqrt n(3+\log(3\sqrt{n/k}))$. The proof of the latter estimate also gives strict consecutive order for the $\lfloor7\sqrt n/20\rfloor$ smallest roots and their reciprocals at every threshold. [Large-threshold proof](effective-threshold.md) · [Exterior roots](effective-front.md) · [Independent review](review-effective-front.md)

For arbitrary cycle counts, a separate estimate bounds both insertion signs at all old roots with $k\sin^2\theta\ge8$, using $t=-\exp(-\pi\cot\theta)$. [Central interval](central-interval.md) · [Independent review](review-central-interval.md)


At $k=3$, the polynomial $E_{n,k}(t)/t$ has $n-2$ simple negative zeros at every $n\ge3$, and they strictly interlace the zeros in the next row. Both conclusions also hold for every $k\ge3$ when $n\ge Bk^2$ for one absolute constant $B$. The zero at the origin is simple. [Original statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Sources and prior work](LITERATURE.md)

The [proof at minimum length three](fixed-threshold.md) compares consecutive rows through their generating function. A [decreasing-run count](small-ranks.md) determines the signs at roots near zero. The [uniform estimate](quadratic-cutoff.md) bounds the dependence on $k$. At $k=3$ the estimates apply from row 400. The proof of existence of the general constant $B$ gives no numerical value. [Manuscript, including the uniform theorem](paper.tex)

**Formal verification · ⬜ None.** An independent research agent reviewed the proof and recorded the finite and uniform checks in two reports. The exact finite certificate covers rows 3 through 401, 398 consecutive pairs and 39,800 dyadic brackets. Inclusion-exclusion reproduces every coefficient vector. Direct enumeration reproduces rows 3 through 8, and clearing denominators verifies all 79,600 endpoint signs. [Certificate](threshold-three-prefix.jsonl.gz) · [Analytic and computational review](review-fixed-threshold.md) · [Review of the uniform bound](review-quadratic-cutoff.md)

For every $k\ge3$, strict interlacing holds for every consecutive pair up to and including the transition from size $3k-2$ to $3k-1$. This covers all pairs for which the new permutation can have at most two cycles. The finite part of the proof checks 3,007 transitions at 379,502 old roots. [Two-cycle theorem](two-cycle-band.md) · [Independent review](review-two-cycle-band.md) · [Finite certificate](two-cycle-finite.md)

The transition from size $2k-1$ to $2k$ is the first one admitting a second cycle. Both signs of its contribution preserve the alternating signs at the old roots. An independent check reconstructed all 118,206 endpoint signs in the finite part of the proof. [Boundary theorem](first-lag.md) · [Independent review and replay](review-first-lag.md)

At the central root $-1$, the insertion term divided by the derivative term is at most $35/68$ in every eligible odd row, with equality only at $(n,k)=(7,4)$. An exact sum of squares test for the remaining reciprocal root pairs succeeds in all 441 previously certified transitions with nonzero insertion term. The all-size question for those noncentral roots remains open. [Sharp central-root theorem](central-insertion.md) · [Two exact trace methods](residue-traces.md) · [Insertion recurrence](insertion-lag.md)

Run the threshold-three checks from the repository root with Python 3.10 or later.

~~~sh
python3 -I -O topics/long-cycle-excedances/verify_threshold_three.py
python3 -I -O topics/long-cycle-excedances/verify_cycle_deletions.py
python3 -I topics/long-cycle-excedances/verify_endpoints.py topics/long-cycle-excedances/threshold-three-prefix.jsonl.gz
~~~

Run the exact scalar checks for the effective bounds from the repository root.

~~~sh
python3 -I topics/long-cycle-excedances/verify_front_constants.py
python3 -I topics/long-cycle-excedances/verify_uniform_effective_constants.py
~~~
