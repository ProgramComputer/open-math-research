# Excedance zeros for permutations with long cycles

The case assembly gives real-rootedness and consecutive interlacing for every fixed minimum cycle length $k\ge3$ and every old size $n\ge k$. It combines ProgramComputer’s proofs for cutoff three and cutoffs at least seven with Bowen Zuo’s independently rebuilt all-size theorems for cutoffs four, five and six. Zuo also gives an independent cutoff-three proof. Joint formal verification is 🟨 Partial · Lean 4. [All-cutoff proof, attribution and verification](all-cutoffs/README.md) · [Large-cutoff manuscript and certificates](all-large-cutoffs/README.md) · [Finite endpoint kernel benchmarks](lean/fast-packed-checks/README.md)

Bowen Zuo’s independent cutoff-seven theorem also covers every original unweighted adjacent pair starting with sizes 7 and 8. The supplying release was independently rebuilt and replayed in Lean 4.33.1. [Cutoff-seven verification](external-verification/cutoff-seven/README.md)

In the large-size exterior range $n\ge10000$, $k\ge8$, $n>4000k$, Lean bounds the insertion lag by one eighth of the old coefficient for $0<p\le\sqrt n/2$. The proof uses the original permutation enumerator and a finite grid of binomial masses. [Coefficient and lag verification](color-load-bounds/README.md)

The [adjacent sine comparison](sine-comparison/README.md) gives an independently reviewed value-only estimate for the middle signs at bounded ratios. Its scalar certificate covers both angle ranges, including sizes where an additional cycle becomes admissible.

The [principal phase and signed angular cells](phase-cells/README.md) have a checked Lean proof on the research pin. For the stated large-size range it gives an ordered set of distinct negative roots of the original row and alternating successor signs. The [uniform coefficient bound](lean/uniform-log-tilt/README.md) controls the Taylor coefficients of the tilt on the enlarged circle at every angle. The [enclosed odd-pole estimate](lean/vertical-tilt/README.md) bounds the positive nonprincipal contribution by one fifth throughout the middle range. The [middle-root sign theorem](lean/middle-residues/README.md) gives the actual successor sign at every old zero under the stated size and angle assumptions. The checked reduction joins the middle and exterior root lists and reduces complete interlacing in its size range to two coefficient inequalities per exterior rank and explicit bounds on the scales. [Theorem, hypotheses and verification](lean/front-middle-join/README.md) The color-acceptance transform identifies an exact binomial transform of the original rows and bounds its coefficient error for the exterior estimates. [Counting proof, Lean scope and finite check](color-acceptance/README.md)

Lean now proves both complete root lists throughout the explicit sector $k\ge8$, $n\ge10000$, $30\log n+20<n/(200k)$. The reduced rows strictly interlace, with the larger row supplying both outer roots. The unreduced rows interlace with their common simple zero. [Theorem, cutoff-only threshold and pinned verification](lean/sparse-sector/README.md)

For every $`7\le k\le n`$ with $`n/k\ge20`$, the nonzero roots of the consecutive rows are simple, negative and strictly interlace. Exact exterior certificates through size 1,000, an exterior estimate through size 9,999 and a common circle comparison fill the gap between the finite prefix and the uniform size 10,000 theorem. The finite intermediate certificate treats the complementary sizes $`251\le n<1{,}000`$ at $`4\le n/k<20`$. Formal verification is ⬜ None. [Combined proof, checks and independent reviews](aspect-20/README.md)

For every $`n\ge1{,}000`$ and $`4\le n/k\le20`$, the nonzero roots of the consecutive rows are simple, negative and strictly interlace. Bounded-aspect exterior and middle estimates give the join through size 9,999. The same package gives a high-angle middle bound from size 251. Formal verification is ⬜ None. [Combined proof, exact checks and independent reviews](bounded-aspect/README.md)

For every $n\ge10{,}000$ and $3\le k\le n$, the nonzero roots of consecutive fixed-threshold excedance rows are simple, negative and strictly interlace. For $n/k<4$ use the three-cycle theorem. Keeping the principal residues handles $4\le n/k\le48$, and two integrations of the common contour handle $n/k\ge44$. The ranges overlap. Formal verification is ⬜ None. [Principal residues and independent replay](paired-residues/README.md) · [Fourier comparison and independent replay](fourier-circle/README.md) · [Lean supporting identities for the paired-residue profile](lean/paired-profile/README.md)

For every $3\le k\le n\le250$, the nonzero roots of consecutive fixed-threshold excedance rows are simple, negative and strictly interlace. An exact certificate covers the remaining 7,021 pairs with $4\le k\le\lfloor n/4\rfloor$. [Finite prefix, replay and independent review](finite-prefix/README.md)

For every $n\ge100{,}000$ and $3\le k\le n$, the nonzero roots of the two consecutive rows are simple, negative and strictly interlace. A joint bound on the polynomial and its angular derivative certifies the required signs. The proof covers eleven intervals in $n/k$ and joins to the differentiated-residue and common-circle estimates. [Theorem, independent review and exact checks](degree-blocks/README.md)

For every $k\ge3$ and $k\le n\le4k-1$, the nonzero roots of the consecutive rows are simple, negative and strictly interlace. This includes the first transition permitting four cycles. [Complete three-cycle range, proof and verification](three-cycle-complete.md) · [Manuscript, Section 12](paper.pdf)

For every $n\ge972{,}000$ and $3\le k\le n$, the consecutive nonzero roots are simple, negative and strictly interlace. The proof differentiates common residues and extends both circle comparisons to the lower phase entrance. [Proof and independent checks](differentiated-residues/README.md)

For every $n\ge4{,}062{,}720$ and $3\le k\le n$, the consecutive nonzero roots are simple, negative and strictly interlace. Adaptive pole bounds for bounded $n/k$, the wider-circle comparison for larger $n/k$, and a separate treatment of thresholds below 400 give this cutoff. [Combined proof and verification](adaptive-poles/README.md)

The earlier uniform estimate covered every $n\ge 250000^2=62{,}500{,}000{,}000$ and every threshold $3\le k\le n$. It compares a truncated logarithm with its value at a smaller radius, then combines two threshold ranges. [Wider-circle proof](radial-taylor.md) · [Independent audit](review-radial-taylor.md) · [Exact scalar checks](verify_radial_taylor.py)

For $n\ge10^{18}$ and every $3\le k\le n$, the consecutive nonzero roots are simple, negative and strictly interlace. A signed pole sum also proves the explicit range $n\ge10{,}000$ and $k\ge2000\sqrt n$. [Uniform pole estimate, proof and checks](uniform-hilbert/README.md)

For every minimum cycle length $k\ge3$, the pair from $3k-1$ to $3k$ has simple negative nonzero roots and strictly interlaces. It is the first pair whose next row can contain three cycles. [All-size transition theorem and exact replay](first-three-cycle-boundary.md) · [Independent review](review-first-three-cycle-boundary.md)

The previous explicit cutoff was $n\ge10^{20}$ for every $3\le k\le n$. Its short-cycle argument gives the separate sufficient condition $n\ge10^6$ and $n/(200k)>30\log n+20$. The proof counts phase crossings and needs no monotonicity assumption. The finite complement remains too large for exhaustive verification. [Proof](effective-uniform.md) · [Independent review](review-uniform-effective.md) · [Earlier existence argument](uniform-interlacing.md)


The previous explicit large-threshold condition for $n\ge10{,}000$ was $k\ge2000\sqrt n(3+\log(3\sqrt{n/k}))$. For every threshold in those rows the first $\lfloor7\sqrt n/20\rfloor$ nonzero roots at each end obey strict consecutive order, including when the condition on $k$ fails. [Effective theorem](effective-threshold.md) · [Extreme-root estimates](effective-front.md) · [Pole estimates and review](review-separated-poles.md)

For $n\ge1{,}000{,}000$ and $20\le n/k\le100$, a run-color coupling increases the exterior range to the first $\lfloor\sqrt n/2\rfloor$ roots in modulus at each end. It gives the actual next-row signs there and a middle join with $n\sin^2\theta>49/20$. [Half-square-root exterior proof](half-root-front/README.md) · [Enhanced middle bounds](half-root-front/middle.md) · [Independent review](half-root-front/review.md)

The wider-circle ratio condition applies from $n=10{,}000$ for $k\ge400$. For $4\le k\le399$, variable radii and a separate Taylor split give simple negative nonzero roots and strict consecutive interlacing for every $n\ge55{,}000$. [Proof, exact replay and independent review](lower-circle/README.md)

For minimum cycle length $k=3$, the reviewed proof gives simple negative nonzero roots and strict interlacing between consecutive rows for every $n\ge3$. Both conclusions also hold for every $k\ge3$ and $n\ge Bk^2$ with one absolute constant $B$. The proof does not give its numerical value. [Uniform cutoff](quadratic-cutoff.md) · [Review](review-quadratic-cutoff.md) All $399$ coefficient vectors in the finite part for $k=3$ were reconstructed independently. The cutoff-three theorem supplies the first case of the complete argument. [Argument](fixed-threshold.md) · [Source and earlier work](LITERATURE.md) · [Alexandersson’s original statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances)

For all sufficiently large $n$, the proposed all-root theorem gives $n-2$ distinct negative zeros and a simple zero at zero whenever the minimum cycle length satisfies $k\ge 100n/\log n$. The bound is uniform over $k\le n$ and permits the maximum number of cycles to grow. [All-root theorem and proof](linear-cutoffs.md)

For each $3\le k\le n$, the proposed theorem gives a simple negative closest nonzero root, strictly between the closest and all the remaining nonzero-root moduli in the next row. Reciprocation gives the largest root. In every sufficiently large row, all ranks through $\lfloor\tfrac14\sqrt{n/\log n}\rfloor$ at either end alternate, uniformly in the minimum cycle length $k$. [Statement and argument](proof.md) · [Alexandersson’s conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsPermutations) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)

**⬜ None.** The arguments are written. Exact integer checks of the extreme-root theorem cover 465 rows and 435 consecutive pairs through size 32. Reproduce the [archive](prefix.jsonl.gz) from the repository root using Python 3.10 or later.

~~~sh
python3 -I -O topics/long-cycle-excedances/verify.py
python3 -I -O topics/long-cycle-excedances/verify_threshold_three.py
python3 -I -O topics/long-cycle-excedances/verify_cycle_deletions.py
~~~

An independent agent-assisted review checked the run encoding, the explicit formula for the second coefficient, the root separation in consecutive rows, and the uniform binomial probability estimate. The new threshold-three certificate supplies 39,800 disjoint dyadic brackets across the 399 rows. The second checker uses inclusion-exclusion on fixed points and transpositions. [Finite certificate](threshold-three-prefix.jsonl.gz)

The independent referee checked the analytic inequalities and reconstructed all 79,600 endpoint signs by clearing denominators. [Referee report](review-fixed-threshold.md) · [Independent sign checker](verify_endpoints.py) · [Manuscript](paper.tex)

The first-cycle-lag theorem gives strict interlacing between rows $2k-1$ and $2k$ for every $k\ge3$. At each old root the new-cycle term is smaller in magnitude than the derivative contribution. The proof uses 19,701 dyadic brackets for $3\le k\le200$ and an analytic bound for $k\ge201$. At $(n,k)=(9,5)$ the sum of the absolute ratios already exceeds two. [Argument](first-lag.md) · [Finite certificate](first-lag-prefix.jsonl.gz) · [Exact checker](verify_first_lag.py)

The insertion recurrence suggests an all-size induction at the old roots. Its sufficient inequality passes all 946 consecutive pairs ending by size 46. [Finite induction test](insertion-lag.md) The central root has a sharp all-size bound of $35/68$. A sum of squares tests the remaining reciprocal pairs. [Central-root proof](central-insertion.md) · [Rational traces](residue-traces.md)

Positive interlacing weights alone allow an insertion ratio greater than four in a synthetic chain with genuine earlier rows. In the genuine rows for $k=3$, a Jacobi compression isolates a small component of the insertion ratio and leaves a signed difference of two weight measures to estimate. [Argument and scope](jacobi-defect.md) · [Exact checks](verify_jacobi_defect.py)

For the quotient of two consecutive transformed rows, the Hankel moment form is positive through degree $\lfloor7k/12\rfloor$ for every $k\ge150$ and $n\ge k$. At $k\ge750$, the associated finite Jacobi compression has spectrum in $(0,1)$. These estimates concern the leading compression. [Uniform moment blocks and exact checks](jacobi-moment-blocks.md) · [Independent review](review-jacobi-moment-blocks.md)

Every consecutive pair before three cycles can occur strictly interlaces, at every admissible threshold. The proof treats both lag signs for $2k\le n\le3k-2$ using 16 rational bounds above the analytic cutoff and exactly 3,007 smaller pairs. [Two-cycle theorem](two-cycle-band.md) · [Independent review](review-two-cycle-band.md)

For $n\ge2{,}200$ and $3k-1\le n<4k$, all nonzero roots of the consecutive rows are simple, negative and strictly interlace. The argument combines separate exterior bounds with a middle estimate over subsets of at most three occupied poles. It includes the pair from $4k-1$ to $4k$. [Three-cycle-band theorem and rational checker](three-cycle-2200.md) · [Independent review](review-three-cycle-2200.md) · [Earlier cutoff at $10{,}000$](three-cycle-poles.md)

For arbitrary cycle counts, every old real root in a specified central interval is simple and meets the strict insertion inequality. There is an explicit lower bound for the number of such roots at every $n\ge k\ge8$. [Central interval and root count](central-interval.md) · [Independent review](review-central-interval.md)

Reproduce the effective bounds from the repository root with the following commands.

~~~sh
python3 -I topics/long-cycle-excedances/verify_front_constants.py
python3 -I topics/long-cycle-excedances/verify_uniform_effective_constants.py
~~~

Marking the cycles gives a continuous deformation from Eulerian rows to the conjectured rows. A resultant detects collisions. In 91 exact cases strict interlacing holds throughout the unit interval, and a symbolic example shows why the unrestricted positive-weight extension fails. [Argument and data](cycle-marking.md)

Bernstein coefficient matrices of the shared-weight Bézoutian certify interlacing on the unit interval for 225 consecutive pairs through old size 34 and for $(n,k)=(48,21)$. An exact negative middle coefficient at $(5376,2560)$ and an infinite family show where that matrix certificate fails. [Proof and scope](bernstein-bezout.md) · [Exact checker](verify_bernstein_bezout.py)

Giving consecutive rows independently chosen cycle weights causes the order of a fixed-rank root to reverse, even for arbitrarily small fixed increases of the weight. The obstruction identifies why adjacent rows need to share the parameter. [Proof and rational witness](independent-cycle-weights.md)

Refining by the image of the largest letter rules out a termwise interlacing induction at every $n\ge2k$. Even the two extreme ranks combined fail the comparison at $n=2k$ for every $k\ge4$. [Terminal-rank identities and exact obstructions](terminal-rank.md)
