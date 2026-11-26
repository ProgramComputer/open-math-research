# Distinct-pole bounds for the bounded-aspect middle

Use the notation of the [degree-block](../degree-blocks/README.md) and [paired-residue](../paired-residues/README.md) proofs. Let $`x=n/k`$, $`A=kS`$, $`U=6/5`$, and restrict to $`nS^2\ge U`$. A box uses aspect endpoints $`\ell,X`$, a minimum row $`N`$, and threshold bounds $`K_0\le k\le K_1`$ when the upper bound is finite. In a low-angle box $`A_0\le A\le A_1`$, we can additionally require $`k\le XA_1^2/U`$. Conversely when $`A\ge A_0`$ and $`k\le K_1`$, use $`nS^2\ge\max(U,\ell A_0^2/K_1)`$. Increase the row lower bound to $`\lceil\ell K_0\rceil`$ when this is larger.

## Distinct factors and their pole tails

Use bins $`i=\lceil Bs/k\rceil`$ with $`B=8`$. For primitive degree $`s`$, use the absolute numerator bin-mass bound $`v_i`$ from the degree-block proof with this bin width. At each signed odd pole $`q`$ retain its own mass and $`\lvert q-a\rvert`$ denominator for a fixed distinguished pole $`a`$. If the box has $`nS^2\ge U_*`$, then the factor $`\rho_q^{s-1}`$ is at most

$$
 W_q((g_i-1/K)U_*/X,E),\qquad
 W_p(d,E)=(1+d(p^2-1)/(2E))^{-E},
$$

for $`g_i\le s/k`$, $`K\le k`$ and $`2E\le K-1`$. Denote this upper bound by $`w_{qi}`$. The absolute primitive mass and its angular derivative divided by $`n`$ are bounded respectively by

$$
 \frac{v_i w_{qi}}{|q-a| A_0},\qquad
 \frac{v_i w_{qi}}{|q-a|}
 \left(\frac{(i/B)|q|}{\ell A_0}+\frac1{KU_*}\right).
$$

Use the product of one factor per retained $`q\ne a`$ and the corresponding product derivative. This retains the distinct-pole restriction. Past $`|q|=P`$, the weighted tail of $`W_q`$ has integral bound
$`(1+c(P^2-1))^{1-E}/(2c(E-1))`$ for $`c=d/(2E)`$, and the mass tail costs at most the weighted tail divided by $`P`$. Bound its gap denominators by $`1/2`$. Exponentiate only the omitted primitive majorant, with its linear derivative factor. For distinguished $`|a|>P`$, switch to the full uniform star majorant and bound the remaining distinguished kernel by the weighted tail. This yields a separate nonnegative pair of binned majorants for every retained $`a`$, and one uniform pair for all $`|a|>P`$.

For a total bin $`b`$, use $`g=\max(1,b/(B+1))`$, $`h=b/B`$, hence $`g\le T/k\le h`$ for nonempty terms. For the empty term use $`g=h=0`$. If $`g+1>X`$ both finite row contributions vanish. The distinguished degrees satisfy $`r/n\ge y=\max(1/X,1-h/\ell)`$ and $`r/n\le1-g/X`$ in the old row. The residual row uses $`y_m=\max(1/X,1-(h+1)/\ell)`$. In the old kernel $`W_a(yU_*,E_n)`$ one may use $`2E_n\le\max(K,Ny)`$. The half-powered off-diagonal kernel uses $`4E_{1/2}\le\max(K,Ny)`$ and argument $`yU_*/2`$. This retains the stronger damping for bins whose distinguished degree is comparable to $`n`$. The residual kernel has analogous exponent $`2E_m\le\max(K,Ny_m)`$. Sum the finite-bin estimates with the two-coordinate matrix bounds of the degree-block proof.

For $`k\ge22`$, the cycle probability bound $`kd_r\le59/100`$ for $`r\ge2k`$ follows from the original tangent and induction proof with that upper bound substituted. The scalar conditions are $`1/22+\log(100/59)<59/100`$ and $`1+\log2+(1+59/100)/22<3(59/100)`$. The lower bound $`kd_r>547/1000`$ for $`r\ge3k`$ follows from the same induction as before using the elementary lower probability $`kd_r>1/2`$ for $`r\ge k`$. These hypotheses also bound $`kd_\infty`$. The two single-pole tails for the high-angle comparison can be bounded directly by the same lattice.

## Principal multiplier for low angles

Take rational bounds $`c_*\le\sqrt{1-(A_1/K)^2}`$ and
$`\tau_*\le\pi c_*/A_1`$. Then $`s/k\ge\tau_*`$. The $`j`$-th real gamma density relative to its maximum at $`k-1`$ is

$$
 \exp\bigl(-(k-1)I(js/(k-1))\bigr),\qquad I(v)=v-1-\log v .
$$

The ratio in $`I`$ lies between $`j\tau_*`$ and $`j\pi K/(A_0(K-1))`$. Bound $`I`$ from below at the point of this interval closest to one, using its monotonicity on each side. The upper gamma-density peak is $`1/\sqrt{2\pi(K-1)}`$. For $`H(s)`$, each Poisson lower tail is at most $`\exp(-K I(\max(1,j\tau_*)))`$. Sum these bounds for finitely many frequencies. Beyond frequency $`J`$ with $`J\tau_*>1`$, the increasing derivative of $`I`$ gives geometric factor $`\exp(-(K-1)\tau_*(1-1/(J\tau_*)))`$. Bound the vertical tilt by $`\exp(A_1^2/(2Kc_*^2))`$. This gives the separate estimates for $`\eta=\pi\sup_v|H'(s+iv)|`$, the multiplier phase, and $`2k|M_1|`$ as in the paired-residue proof.

For the insertion multiplier one may use absolute pole mass, or for $`\tau_*>1`$ the Eulerian expansion

$$
 |B_k|\le (r/s)^k s\sum_{j\ge1} e^{-js}(js)^{k-1}/(k-1)! .
$$

It follows by expanding the simple-pole identity in $`e^{-s}`$. If $`K I(\tau_*)\ge1`$ and $`\tau_*>1+1/(K-1)`$, the factor $`s`$ can be bounded explicitly. At fixed $`k`$ the function $`s\exp(-(k-1) I(s/k))`$ decreases on $`s\ge k\tau_*`$. At $`s=k\tau_*`$ the bound $`k\tau_*\exp(-(k-1)I(\tau_*))`$ decreases with $`k\ge K`$. Estimate the remaining frequency sum by the geometric tail just described and use the gamma peak and vertical tilt bounds. In both approaches the lag multiplier is $`\lvert B_k\rvert/(nS)`$.

Apply the signed principal continuation and infinite tail argument of the paired-residue proof. At weight $`\lambda>1`$ the bin tail after $`b_*`$ is bounded by $`\lambda^{-b_*-1}`$ times the absolute exponential majorant, its degree-weighted derivative, and the angular derivative majorant. The finite nonprincipal and principal-continuation errors enter the same unrotated phase projection. The checker computes all formal nonnegative bin series with outward fixed-point rounding. Integer packing computes the products exactly on the grid before rounding each output coefficient upward. No arithmetic between coefficient fields can carry because the field size exceeds length times the product of the maximum input coefficients.

## Full cover at old size 1,000

**Theorem.** At every old size $`n\ge1{,}000`$ and aspect $`4\le x\le20`$, the integer-phase values have alternating signs in the angular middle $`nS^2\ge6/5`$, and both signed insertion comparisons have the derivative's sign at every old root there. In particular the actual consecutive row has the prescribed strict sign in each middle gap. The claim supplies the middle signs. A separate exterior certificate is needed for a global interlacing conclusion at this height.

Use the [narrow replay](narrow.md) on $`[4,15/2]`$. On the remaining aspects, use the high-angle entrances in the table. For smaller $`A`$ in each row, partition the interval between the hundredth-grid lower entrance and that displayed entrance at half-integer points, using the paired principal comparison on each closed subinterval.

| Aspect | High-angle entrance for $`k\le100`$ | High-angle entrance for $`k\ge100`$ |
| --- | ---: | ---: |
| $`[15/2,10]`$ | $`9/2`$ | $`5`$ |
| $`[10,14]`$ | $`9/2`$ | $`11/2`$ |
| $`[14,18]`$ | $`4`$ | $`11/2`$ |
| $`[18,20]`$ | $`4`$ | $`11/2`$ |

The hundredth-grid entrance is rounded downward from $`\sqrt{(6/5)\max(1000/X^2,K_0/X)}`$. The low-angle scalar code discards boxes with no feasible $`k`$. Each of the eight high-angle bounds exceeds $`45932/10^6`$. The low-angle bounds, scaled by the principal amplitude, exceed $`286423/10^6`$. The lower threshold guard $`k\ge22`$ used in the derivation is automatic here since $`n\ge1{,}000`$ and $`x\le20`$ imply $`k\ge50`$.

Run `python3 -I -B verify-1000.py` from this directory. The [proof arithmetic](check-grouped.py) uses only the Python standard library, and the [recorded output](replay-1000-exact.txt) gives individual margins. The independent [small-aspect checker](check-narrow.py) covers $`[4,15/2]`$.
