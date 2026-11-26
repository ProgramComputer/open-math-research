# Independent dyadic sample audit

The audit uses selected pairs from $192\le n<2200$ and $3k-1\le n<4k$, covering each of the 19 exterior ranks for every selected pair. Its sample includes rows near both ends of the size range and rows near the lower, middle and upper parts of the threshold band. It includes transitions that first admit three or four cycles.

The first 48 coefficients of the old and new rows are constructed separately by distinguishing the cycle containing the least label, and summing its length against the residual single- or two-cycle enumerator. At size $4k$ the all-equal four-cycle term is added. The negative pencil subtracts twice the lag for a new cycle of length $k$ formed from the independently constructed residual row. This construction differs from the insertion recurrence used by the full exterior checker. The four relevant Eulerian prefixes are additionally checked against their exact power-sum finite-difference formula.

The original Arb checker proposes two phase indices for each bracket. Arb encloses the phase modulus, and truncation of the exact binary lower endpoint to at most 96 mantissa bits gives a positive dyadic below that modulus. The audit certifies signs of the resulting dyadic brackets directly. It checks that the 19 brackets are strictly separated, and that the last right endpoint is below or equal to the certified lower radius of phase 20. It checks the opposite old signs and the two common signed-pencil signs at both endpoints. No Arb polynomial sign is used to accept a dyadic endpoint.

For modulus $u/2^d$, each fixed-point Horner step computes the displayed integer recurrence

$$
V_i=c_i2^B-\left\lfloor uV_{i+1}/2^d\right\rfloor,
\qquad B=128.
$$

Each step contributes less than one unit of rounding error on this scale. Since the modulus is below one and there are 48 coefficients, the total error is strictly below 48. The absolute omitted coefficients, including those of the signed pencil, are bounded by $p^N$, with $N=n$ for the old row and $N=n+1$ for either next pencil. Put $a=d-\mathrm{bitlength}(u)$, so the modulus is less than $2^{-a}$. If $2^{a-1}49^N\ge50^N$, the successive omitted term ratios are at most $1/2$. The scaled omitted tail is then bounded by $\lceil49^N2^{1+B-48a}\rceil$. The checker requires the absolute fixed-point value to exceed the sum of the rounding and tail bounds. It falls back to the exact homogeneous Horner and geometric-tail inequality in the [exact dyadic sign routine](three_cycle_dyadic_sign.py) if the shortcut is inconclusive.

Run with Python-FLINT, passing the path to the original bracket proposal script.

~~~sh
python3 -I verify_three_cycle_dyadics.py check-three-cycle-exterior.py
~~~

The audit is sampled. The full-band coverage comes from the separate exhaustive Arb replay. An all-pair dyadic replay can avoid repeating the phase search by exporting the two accepted phase indices per bracket from the full checker and applying the integer sign procedure directly.

The complete stratified replay passed on 29 pairs, with 551 dyadic brackets and 3,306 integer-only polynomial signs. The sample contains all four selected high-end pairs $(2198,733)$, $(2199,550)$, $(2199,628)$ and $(2199,733)$.
