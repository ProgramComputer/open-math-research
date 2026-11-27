# Exact long-cycle excedance interlacing through size 250

For every $3\le k\le n\le250$, the nonzero roots of the minimum-cycle-length excedance rows at $n$ and $n+1$ are simple, negative and strictly interlace. The computation checks the remaining 7,021 pairs with $4\le k\le\lfloor n/4\rfloor$. The earlier results cover old size $n\le4k-1$ at each threshold and all sizes at $k=3$. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4) · [Three-cycle theorem](../three-cycle-complete.md) · [All-size threshold-three proof](../fixed-threshold.md)

**Formal verification** ⬜ None. The finite calculation uses certified signs and exact rational fallbacks. [Independent review](review.md)

## Exact polynomial and change of coordinate

Write $Q_{n,k}=E_{n,k}/t$, where $E_{n,k}$ sums the excedance monomials over permutations whose cycles all have length at least $k$. For each fixed ordered label set of size $\ell$ the weighted sum over single cycles is $tA_{\ell-1}(t)$. To see this, write the cycle starting at its greatest label and read the remaining entries in cycle order. The greatest entry contributes no excedance, its predecessor contributes one, and on the other edges excedances are ascents of the remaining word. The distribution of ascents equals the Eulerian distribution.

The cycle containing the least label gives the exact recursion

$$
Q_{n,k}= A_{n-1}+t\sum_{\ell=k}^{n-k}\binom{n-1}{\ell-1}A_{\ell-1}Q_{n-\ell,k}.
$$

Set $d=n-2$. Multiplying the basis elements $t^j(1+t)^{d-2j}$ adds their indices and their formal degrees. Thus the recurrence works directly in the gamma variable with the same binomial factors and a shift by one in every summand with two factors. For $A_r$ at formal degree $r-1$, its usual Eulerian recurrence gives

$$
g_{r,j}=(j+1)g_{r-1,j}+2(r-2j)g_{r-1,j-1}
$$

with $g_{1,0}=1$ and zero out-of-range coefficients. In particular the reduced row has degree $d$, is reciprocal, and has constant and leading coefficient one. Its gamma polynomial $G_{n,k}$ has degree $\lfloor d/2\rfloor$ by its single-cycle contribution, and the checker also tests the degree explicitly.

On $0<y<1$,

$$
Q_{n,k}(-y)=(1-y)^dG_{n,k}\left(-\frac{y}{(1-y)^2}\right).
$$

The map $v=y/(1-y)^2$ is strictly increasing onto $(0,\infty)$. A strict bracket for a positive root of $G_{n,k}(-v)$ gives one negative root in $(-1,0)$ and one in $(-\infty,-1)$ by reciprocation. For odd $d$, there is also exactly one central root $-1$, because the top gamma coefficient is nonzero. For even $d$, the same coefficient gives a nonzero value at $-1$.

## Sign certificate

The constant term in the gamma coordinate is one. For each old row the checker maintains sorted disjoint strict rational brackets, one for each positive gamma root, with alternating endpoint signs. The number of brackets equals its gamma degree, so there are no additional roots or multiplicities. For the next row it refines each old bracket until both endpoints have the expected next-row sign $(-1)^i$, where $i$ starts at one in increasing $v$ order. It then constructs new brackets in $(0,a_1)$ and each $(b_i,a_{i+1})$, where $(a_i,b_i)$ is the refined old bracket. If the new gamma degree increases by one, it also requires a strict bracket beyond the last old bracket. In each new bracket the endpoint signs are opposite by construction. Explicit zero evaluation at an old midpoint is handled by shrinking both endpoints towards it. The old bracket already contains just one root, so the signs on either side are preserved. All arithmetic in the endpoints is exact.

If the old degree $d$ is even, both gamma rows have the same degree. New then old roots alternate in increasing $v$, and the new row has the central root. If $d$ is odd, the new gamma row has one more root, including the extra bracket toward $v=\infty$. The old row has the central root. Both orders give strict consecutive interlacing after reflection. The constant row at size 3 supplies degree-zero bootstrap brackets for the single-cycle sequence. Subsequent sizes before $4k$ are used to propagate the brackets.

For a sign query, Python-FLINT evaluates the polynomial at the rational point using certified Arb enclosure arithmetic. If the enclosure excludes zero, its sign is rigorous. Otherwise the checker evaluates the same polynomial as a rational number and compares to zero exactly. No root solver or Sturm chain is needed. The loop limit causes a hard failure if sign brackets fail to separate.

The independent coefficient checker constructs rows by adding cycle lengths in succession with the exact multinomial factors for repeated cycles. It computes ordinary Eulerian polynomials from a separate coefficient recurrence, expands the gamma side back to ordinary coefficients, and requires full vector equality.

## Replay

Run from this directory with Python-FLINT 0.9.0 and FLINT 3.6.0. The certificate cap is inclusive on the old size, so these runs include the next row at size 251. The coefficient cross-check uses 101 as its row-size cap.

```sh
python -B certify.py 250
python -B certify-rolling.py 250
python -B cross-check.py 101
python -B verify-independent.py
```

The independent check enumerates cycle partitions, compares 37 full vectors against the certifier, and uses Sturm chains directly on the original polynomials to isolate 436 roots across ten sample pairs. [Representative check output](independent-output.txt) · [Full independent rolling replay](independent-rolling-replay.txt) · [Ordinary-vector replay](independent-cross-check-replay.txt)

This is an exact finite calculation. A whole range beyond the tested cap would require a further completed replay or a theorem.

## Completed range and performance

Both complete replays certify all 7,021 pairs with $4\le k\le \lfloor n/4\rfloor$ and old size $n\le250$. The pair count is $\sum_{k=4}^{62}(251-4k)$ and the old-root count is $\sum_{k=4}^{62}\sum_{n=4k}^{250}(n-2)=1{,}190{,}089$. Together with the published all-size $k=3$ and $n\le4k-1$ results, this covers every allowed threshold through old size 250. The logs report 4,603,257 sign queries and three exact rational fallbacks. The counters include setup from row size $k$ through $4k-1$ and exclude transient single-cycle bootstrap objects below size $k$. The independent ordinary-vector calculation checked 1,925 full rows through size 101. [Ordinary coefficient log](cross-check-output.txt)

| Coefficient generation | Wall time | Maximum resident set size | Output |
| --- | ---: | ---: | --- |
| Cycle containing the least label | 86.51 s | 38.6 MB | [Sign log](output-250.txt), [timing](resource-250.txt) |
| Descending cycle-length threshold | 37.98 s | 40.1 MB | [Sign log](rolling-output-250.txt), [timing](rolling-resource-250.txt) |

The rolling engine takes the rows at threshold $k+1$ and adds $h$ cycles all of size $k$ with multiplicity $\binom{n}{hk}(hk)!/((k!)^h h!)$. Raise the cycle gamma polynomial to power $h$, multiply by the residual gamma row, and shift the result by $h$. If the residual is empty the shift is $h-1$, accounting for removing the common $t$. Updating row sizes in descending order keeps the residual at threshold $k+1$ until it is used. Both runs matched the pair counts, root counts and sign-query counts separately at all 59 thresholds. The coefficient generation and ordinary-vector cross-check are distinct from the root certificate, which both benchmark runs share.

In the rolling run the sum of reported generation times is a small fraction of total time. The outstanding cost is repeated signed evaluation, and the measurement at 250 does not establish feasibility through the published analytic cutoff.

The cutoff-eight pairs with $32\le n\le250$ also have a [dyadic certificate in the original polynomial variable](dyadic-windows/README.md), with a separate exact verifier.
