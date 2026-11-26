# Lean check of the strict Catalan peak sign transfer

Lean defines the strict-peak counting polynomial directly by enumerating
Catalan words. Words have zero first letter and adjacent increases at most
one. The bound on each letter identifies the finite alphabet with the
original nonnegative-integer word definition. Strict peaks use three
consecutive letters with the middle letter strictly largest. [Alexandersson's conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjCatalanWordPeaks) · [Baril et al., definition and generating function](https://arxiv.org/html/2404.05672v1#S5.Thmtheorem1)

The unconditional combinatorial results are in [CatalanStrictPeaks.lean](CatalanStrictPeaks.lean).
Theorem `coeff_C` gives each coefficient as the cardinality of the set of
valid words with that peak count. Theorems `eval_zero_pos`, `leadingCoeff_pos`,
and `natDegree_C` give both endpoint signs and the degree
$\lfloor(n-1)/2\rfloor$, with natural subtraction for the empty word. The
degree bound pairs each peak start with its successor. The alternating
word $0101\cdots$ attains the bound.

The reusable [OrientedNegativeInterlace.lean](../../../shared/lean/OpenMathResearch/OrientedNegativeInterlace.lean)
uses the shared alternating-sign root lemmas for both degree patterns.
If the old positive root moduli in increasing order are $o_1,\dots,o_m$ and
the new ones are $v_1,\dots,v_d$, the output gives $v_i<o_i$ for every $i\le m$
and $o_i<v_{i+1}$ whenever $i+1\le d$. For a nonconstant old row, the new rightmost negative zero is farther right.
The old farthest modulus exceeds every new modulus in the equal-degree case.
With a degree increase, it lies between the final two new moduli.

[CatalanStrictPeaksInterlacing.lean](CatalanStrictPeaksInterlacing.lean) applies
the reusable result to the exact Catalan polynomial in two stages.

- `roots_from_checkpoints` takes the normalized phase with left
  value $1/4$ and right value $n/2-1/8$, an increasing positive modulus
  parametrization on the open interval, and the strict signs at integer phase
  levels $1\le k<\deg C_n$. Its proof constructs the ordered samples using
  continuity and uses the constant and leading signs to exhaust the degree.
- `next_from_old_root_signs` takes the complete increasing modulus list of
  the simple negative zeros of $C_n$ and the sign $(-1)^i$ of $C_{n+1}(-o_i)$.
  It concludes the directed strict interlacing and the full next root multiset.
- `interlacing_from_finite_and_analytic_signs` records the split at $n=150$.
  Its hypotheses include the strictly interlacing pairs for old rows $n<150$.
  For $n\ge150$ it takes the checkpoint package and the strict signs at
  every old root.

**Partial Lean verification.** The analytic estimates for the checkpoint and old-root signs and the finite prefix of interlacing pairs remain open in Lean. The modules below verify the generating function and the exact word coefficients used by those arguments.

## Exact recurrence on heights and preceding ascents

The [recurrence module](CatalanStrictPeaksRecurrence.lean) proves that a
finite-state transfer computes the strict-peak polynomial for every word length.
A state has height $h$ and a Boolean recording the previous ascent. Appending
$x\leq h+1$ records the ascent $h<x$ and adds a peak exactly when the old
flag records an ascent and $x<h$. The proof bijects the extensions with the
new Catalan words and verifies the update of the peak count. The theorem
`enumerate_X_eq_C` identifies the transfer polynomial with the word
enumerator.

The executable function `coefficients n` returns the coefficient list in
increasing power order. It evaluates the recurrence once at
$q=(n+1)^n+1$, which exceeds the count in any coefficient. The theorem
`coefficients_get_eq_C` proves that integer digit extraction in this base
recovers each coefficient of the original polynomial. Each materialized row
contains two counts per height, and each step examines a quadratic number of
state pairs. The algorithm avoids enumerating the words.

The recurrence and coefficient recovery are kernel-checked at every length.
[Recurrence kernel output](recurrence-kernel.txt)

## First-return generating function and scaled discriminant

The [first-return module](CatalanStrictPeaksFirstReturn.lean) proves the
bijection $w=0(u+1)v$, with the suffix beginning at the first later zero
when present. Its exact peak-count formula includes the possible boundary
peak when the suffix is nonempty and the positive block is a singleton or
ends in a strict ascent. A peak-preserving final rise counts these blocks
by the shorter word family. The resulting coefficient convolution gives
`generatingFunction_eq` for the
[formal series](CatalanStrictPeaksGeneratingFunction.lean) of the original
polynomials. [Published generating-function identity](https://doi.org/10.26493/2590-9770.1794.fc5)

The [discriminant module](CatalanStrictPeaksDiscriminant.lean) checks that
the scaled series has coefficients $c^nC_n(1-c^{-2})$. It proves its quadratic
equation and constructs a formal square root, with constant term one, of
$(1+x^2)^2-4cx$ for $c\ne0$. Convergence, analytic branch continuation and
the sign estimates remain in the analytic proof.
[Generating-function kernel output](generating-function-kernel.txt)

[Written proof](../proof.md)

## Build

Run from the [shared Lean project](../../../shared/lean/README.md) with pinned
Lean and mathlib.

~~~sh
lake build OpenMathResearch.OrientedNegativeInterlace CatalanStrictPeaks CatalanStrictPeaksInterlacing
lake env lean -j1 ../../topics/catalan-word-peaks/lean/Axioms.lean
lake build CatalanStrictPeaksRecurrence
lake env lean -j1 ../../topics/catalan-word-peaks/lean/RecurrenceAxioms.lean
lake build CatalanStrictPeaksFirstReturn CatalanStrictPeaksGeneratingFunction CatalanStrictPeaksDiscriminant
lake env lean -j1 ../../topics/catalan-word-peaks/lean/GeneratingFunctionAxioms.lean
~~~

[Kernel output](kernel.txt)
