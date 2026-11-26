# Finite middle-root certificates between the exterior and high-angle bounds

Fix $`251\le n\le1000`$ and $`7\le k`$ with $`4\le n/k<20`$. Put $`P_N=E_{N,k}/t`$, where the enumerator counts excedances in permutations whose cycles have length at least $`k`$. The finite calculation supplies a root and its actual next-row sign in each angular gap between the exterior and high-angle inputs.

## Selecting the entrance

Let $`H=\lfloor7\sqrt n/20\rfloor`$ and set $`\theta_j=j\pi/n`$. The [exterior certificate](../aspect-20/finite-exterior/README.md) verifies $`H`$ negative simple roots, their signs in the actual $`P_{n+1}`$, and their position before $`(H+5/6)\pi/n`$. From the [high-angle table](../bounded-aspect/high-251.md) use cutoff $`A=7`$ for $`4\le n/k\le15/2`$, $`A=5`$ for $`15/2<n/k\le10`$, and for $`10<n/k<20`$ use $`A=5`$ if $`k\le100`$ and $`A=6`$ otherwise. Let $`J`$ be the first tested integer $`j\ge H+1`$ for which

$$
k\sin\theta_j\ge A,\qquad n\sin^2\theta_j\ge6/5.
$$

The checker verifies both inequalities using outward-rounded real balls. The choice of the earliest certified integer is an optimization. Any later certified entrance works if all additional intervening ranks are covered. Monotonicity of sine on the first half-axis makes the high-angle inequalities valid from $`\theta_J`$ through $`\pi/2`$. In this range the high-angle argument gives alternating signs at integer phase samples and the actual next-row sign at each old root in an open integer gap.

## Certificate in each intervening gap

For each integer $`H+1\le j<J`$, put $`y_j=\exp[-\pi\cot(\theta_j)]`$. The checker finds positive dyadic endpoints $`a<b`$ inside the gap in modulus. It requires

$$
\begin{aligned}
y_j&\le a<b\le y_{j+1},\\
(-1)^{j+1}P_n(-a)&>0,\\
(-1)^{j+2}P_n(-b)&>0,\\
(-1)^jP_{n+1}(-y)&>0\quad (a\le y\le b).
\end{aligned}
$$

The old-root interval in fact lies strictly inside $`(y_j,y_{j+1})`$ because neither $`a`$ nor $`b`$ is a zero. The inequalities establish one old zero by continuity and its required next-row sign. They require neither local uniqueness nor trusted numerical root approximations. Even if several roots were compatible with an isolated test, the degree exhaustion below proves uniqueness. The checker also confirms the old signs at its rounded sample endpoints.

To check the inequalities, compute the first $`W=64`$ coefficients of $`P_N`$ exactly. The omitted coefficients satisfy $`[t^p]E_{N,k}\le p^N`$. Indeed, a permutation at exponent $`p`$ has $`p`$ decreasing runs on its cycles, obtained by cutting at the excedance edges. The assignment of labels to $`p`$ distinct run colors and the successor permutation on the colors determine the original permutation. Each permutation has $`p!`$ run labelings among at most $`p^N p!`$ such labeled pairs. The bound follows by division.

For $`y\le y_{j+1}`$ and for either $`N=n`$ or $`N=n+1`$, the checker bounds the omitted absolute sum by

$$
\frac{(W+1)^N B^W}{1-B((W+2)/(W+1))^N},
\qquad B\ge y_{j+1}.
$$

It checks that the denominator is positive. The bound holds because the ratio of successive terms $`p^Ny^{p-1}`$ decreases with $`p`$. The initial term occurs at $`p=W+1`$ because the common factor $`t`$ has been removed. For both polynomial endpoint evaluations and the whole new-row interval, use Horner evaluation of the signed coefficients with Arb. The evaluation ball must be separated from zero by more than the certified tail. In particular, same-signed new endpoint values are insufficient on their own. The program verifies the sign of the actual new row on the entire real interval.

Approximate Newton iterations only propose dyadic bracket endpoints. Each proposed bracket must pass the displayed rigorous inequalities. When a candidate fails, bisection maintains the two strict old endpoint signs and tests the new row on the remaining interval. The starting endpoints are the upper and lower enclosures of $`y_j`$ and $`y_{j+1}`$, respectively. The recorded digests identify the certified endpoints by integer mantissas and binary exponents.

## Exact coefficient construction

The contribution on a fixed $`\ell`$-label single cycle is $`tA_{\ell-1}(t)`$, with $`A`$ the Eulerian polynomial. The code generates ordinary Eulerian prefixes by their usual insertion recursion. At high thresholds it lowers the cutoff from $`k+1`$ to $`k`$ and adds all repetitions of the newly permitted cycle length $`k`$. Adding $`a`$ cycles of length $`k`$ uses multiplicity $`\binom{N}{ak}(ak)!/((k!)^a a!)`$. On the reduced polynomials the power shift is $`a`$ when the residual row is nonempty and $`a-1`$ when it is empty. Updating sizes in descending order preserves the old residual row. At lower thresholds the program uses the cycle insertion recurrence directly. All polynomial operations in both constructions preserve the exact truncated coefficient vector.

## Joining the three ranges

The exterior verifies ranks $`1`$ through $`H`$. The finite certificate chooses an old zero in each gap $`H+1`$ through $`J-1`$, where a gap has index $`j`$ if its endpoints are $`\theta_j`$ and $`\theta_{j+1}`$. The high-angle argument chooses an old zero in each gap $`J`$ through $`\lfloor n/2\rfloor-1`$. All selections are disjoint and ordered in modulus. The given signs of the new row on that side alternate as $`(-1)^j`$ at the selected index $`j`$.

Reciprocity reflects the half-axis selections. If $`n`$ is odd, the old row also has its forced root at $`-1`$, where the high-angle sign supplies the central next-row sign. In either parity this accounts for exactly $`n-2`$ distinct old roots, the degree of $`P_n`$. Hence they are all simple and the selected signs run over every old root. The signs at zero and at the far negative end of the next row, together with its alternating values at the old roots, give $`n-1`$ distinct negative zeros meeting strict consecutive interlacing.

This certificate needs the exterior proof and the high-angle argument as stated above. The finite replay itself does not establish either analytic input.

## Replay

Use Python-FLINT 0.9.0 with FLINT 3.6.0. Run `python -B check.py` from this directory, with assertions enabled. The expected counts are 93,902 pairs and 541,199 finite middle gaps, and the maximum entrance index is 33. Pairs with $`J=H+1`$ obtain their entire conclusion from the two analytic or previously certified inputs. The file `entrance.py` counts the eligible pairs and required ranks using only the angular entrance test. After completing the replay, run `python -B verify-output.py` to match every individual threshold record to that coverage and verify that the rounded phase endpoints are ordered.

The optional [rational fixture replay](check-fixtures.py) rebuilds the prefixes by a separate coefficient implementation. It checks the candidate endpoints and full new-row intervals with rational Horner bounds instead of Arb. Its [output](fixtures-output.txt) records 80 checked gaps across five fixtures.

The complete run passed all 93,902 pairs, including 82,395 with finite gaps. It certified 541,199 intermediate roots and their actual next-row signs in 333.87 seconds of wall time with 116.2 MB maximum resident memory. The [main log](output.txt) and [coverage replay](verified-coverage.txt) record these checks.

## Independent separating-point check

The second program tested the same 93,902 parameter pairs and all 541,199 intervening ranks. It uses 60 coefficients, 160-bit Arb arithmetic, and ordinary bisection. For the pair of reduced polynomials $`f=P_n`$ and $`g=P_{n+1}`$ it finds two positive points $`a<b`$ within each required phase gap of index $`j`$, with the four strict signs

$$
(-1)^{j-1}f(-a)>0,\quad (-1)^jf(-b)>0,\qquad
(-1)^jg(-a)>0,\quad (-1)^jg(-b)>0.
$$

The interval $`[a,b]`$ contains an old zero. Between consecutive closed brackets the two nearest endpoints have opposite new-row signs, so the complementary gap contains a new zero. Treat the old exterior and high-angle roots with known next-row signs as one-point brackets. Reflection preserves the separation, since $`P_{n+1}`$ has known parity of its degree in the reciprocity identity. The signs at zero and at the far negative end give the two outer new zeros. The resulting $`n-1`$ disjoint gaps exhaust the new degree, establishing strict consecutive interlacing. This argument uses only point values of the new row.

The second implementation builds all prefixes at each fixed cutoff by insertion and obtains the single-cycle Eulerian coefficients by their finite-difference formula. A separate decomposition by the cycle containing the least label reconstructed 720 exact coefficient entries from six pairs, including the joins at $`n=4k`$ and at the first checked size. The selected entries consist of 60 consecutive coefficients from each of the two rows. The exact rational fixture check for the primary method also verified 80 gaps from five pairs.

~~~sh
python -B cross-check/verify.py
python -B cross-check/cycles.py
python -B check-fixtures.py
~~~

[Second sign ledger](cross-check/independent-output.txt) · [Cycle decomposition results](cross-check/cycle-output.txt) · [Rational fixtures](fixtures-output.txt) · [Primary sign ledger](output.txt) · [Finite coverage record](verified-coverage.txt)
