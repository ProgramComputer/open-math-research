# Coarse nine-slab product certificate

Let $F=2^{32}$ and $G=2^{56}$. Each slab uses a single signed-star cap, rounded upward to a multiple of $1/256$. In increasing slab order the numerators are 228, 278, 331, 368, 397, 421, 441, 453 and 463. The kernel checks these against the actual maximum over the signed head plus the half-tail at the slab's smallest degree shape. The star decreases as the degree shape increases. The resulting lifted coarse linear coefficients dominate the full original linear table.

The coarse ledgers fix $Q_0=F$ and satisfy

$$
\sum_{i=1}^{b} i L_iQ_{b-i}\le bFQ_b
\qquad(1\le b\le240).
$$

To keep the certificate small, each checker computes a dot product by walking the coefficient prefix and the reversed companion prefix sequentially. Lean proves that this calculation equals the antidiagonal convolution. Each slab's 240 inequalities are checked in ten independent groups of 24. The literal $L_i$ array is separately identified in the kernel with the ceiling formula for all 241 bins.

Multiplying both arrays by $2^{24}$ puts the certificate on the original scale. Positivity and the checked entrywise inequality on the linear coefficients give the actual recurrence inequality against the lifted $Q$. The exact outward recurrence is therefore dominated through bin 240. The underlying literal original-row error theorem can take this $Q$ directly without a premise connecting an executable evaluation to a frozen table.

The independent generator uses Python integer division with remainder and exact fractions. Its comparison checks every frozen $L,Q$ cell. The hosted Lean replay checks the source-linked recurrence and scale transfer separately. Bounds for the other sign-comparison costs use the same $Q$ but are outside this recurrence package.

Run the [independent generator](generate-coarse-ledger.py) with `--check` and this directory as the argument. The [paired-profile driver](check.py) runs it after replaying the declarations.

Local Lean 4.19.0 at Mathlib `c44e0c8` checked [the nine star maxima](CoarseStarCertificate.lean), [the sequential convolution identity](CoarseProductSequential.lean), all nine recurrence shards, and [the original recurrence and rounded-coefficient comparison](CoarseOriginalLedger.lean) with standard axioms only. The nine shards took 406.67 seconds total, with a maximum of 49.33 seconds per shard. The local comparison used the same `linearHead_eq` via a private import. This package exposes that equality for the shared production import.
