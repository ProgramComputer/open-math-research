# Checked Lean components

The [finite formalization](PrismSplit.lean) proves nonalternation of the two coefficient lists computed by grouped inclusion–exclusion and finite differences at \(a=6\). It uses an intermediate value argument and positivity after translating the larger polynomial. The file proves that its enumerator lists each bounded integer composition once and that its dynamic program counts these lists. The [direct count certificate](PrismCounts.lean) uses that dynamic program to verify all 23 dilations needed for the two full coefficient vectors. Its theorem `PrismSplit.compositionRowsDoNotInterlace` proves the obstruction for the numerator evaluations computed from those counts. The [infinite-family formalization](PrismFamily.lean) proves the binomial coefficient gap for every parameter \(b=a-1\ge6\), and applies mathlib's Vieta theorem to rule out alternating negative roots of monic split polynomials with those next coefficients.

The mathematical manuscript identifies the box-slice lattice points, the dimensions and the Ehrhart interpretations of the relevant coefficients. Those generic geometric and Ehrhart theorems are outside the formal scope of this release.

From this directory with Lean's toolchain manager available, run the following.

~~~sh
lake update
awk '/^import Mathlib[.]/ {print $2}' *.lean | sort -u | xargs lake exe cache get
lake build PrismSplit
lake env lean -j1 PrismCounts.lean
lake env lean -j1 PrismFamily.lean
~~~

The project pins Lean and mathlib 4.19.0. For a macOS linker failure in the compiled cache utility, run the interpreted cache utility from the mathlib checkout with `lake env lean --run Cache/Main.lean get` followed by the directly imported mathlib module names. The proof files print axiom dependencies for their main theorems.

The [kernel log](../verification.json) records the source digests, checker version and printed axiom dependencies for this release.
