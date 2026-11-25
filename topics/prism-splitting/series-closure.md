# Whole-series verification of the prism split

For the bound vectors $c=(1^{10},2)$ and $c'=(1^{12})$, let $L_c(q)$ count the integer points in the $q$th dilation of the slice with prescribed sum $6$. Write $D=|c|-1$, where $|c|$ is the number of coordinates, and define

$$
S_c(t)=(1-t)^{D+1}\sum_{q\ge0}L_c(q)t^q.
$$

The Lean proof constructs the two integer polynomials that are equal to these full formal power series and excludes weak alternation of complete real root lists for their evaluations. The box-slice dimensions used for the Ehrhart interpretation are $10$ and $11$. The midpoint is strict in every bound inequality, so each slice has full dimension in its sum hyperplane. [Prism geometry](lean/PrismGeometry.lean) · [Series closure](lean/PrismSeriesClosure.lean)

## Why the coefficients vanish above the dimension

For a fixed dilation $q$, bounded compositions give

$$
L_c(q)=[z^{6q}]\prod_i(1+z+\cdots+z^{q c_i})
      =[z^{6q}]\frac{\prod_i(1-z^{q c_i+1})}{(1-z)^{D+1}}.
$$

For a subset $J$ of the coordinates, set $a_J=\sum_{i\in J}c_i$ and $b_J=|J|$. Its signed term uses the coefficient at exponent $(6-a_J)q-b_J$ in $(1-z)^{-D-1}$. If $a_J\ge6$, this exponent is always negative since $b_J>0$. Otherwise $b_J\le a_J\le5$ and $D-b_J\ge0$. The signed term is then exactly

$$
(-1)^{b_J}\binom{(6-a_J)q+D-b_J}{D}
$$

for every $q\ge0$. The binomial coefficient with nonnegative top entry below $D$ is zero, as required for a negative exponent. Lean groups the identical unit bounds using the binomial theorem.

For any nonnegative integers $a,b$, the step-one forward difference of $q\mapsto\binom{aq+b}{D+1}$ equals $\sum_{i=0}^{a-1}\binom{aq+b+i}{D}$ by Pascal's identity. Thus $D+1$ successive forward differences annihilate each term in $L_c$ and therefore annihilate their sum. For $m\ge0$, the coefficient at $q+m$ in $(1-t)^m\sum_i L_c(i)t^i$ equals the $m$th forward difference of $L_c$ at $q$, by induction on $m$. Taking $m=D+1$ proves the entire normalized series has degree at most $D$.

## Kernel check

The principal statements are `PrismSplit.unsplitEhrhartSeries`, `PrismSplit.splitEhrhartSeries`, and `PrismSplit.ehrhartPolynomialsDoNotInterlace`. The two identities hold as equalities of formal power series over the integers. The noninterlacing theorem uses the polynomial evaluations and follows from the degree bounds proved in the same file. The earlier coefficient certificates supply the exact coefficients through the degree bounds and the sign separation.

With `elan` on `PATH`, run from the `formalization` directory. The project pins Lean and mathlib to 4.19.0.

```sh
lake update
awk '/^import Mathlib\./ {print $2}' PrismSplit.lean PrismCounts.lean PrismGeometry.lean PrismSeriesClosure.lean | sort -u | xargs lake exe cache get
mkdir -p .lake/build/lib/lean
export LEAN_NUM_THREADS=1
lake env lean -j1 -o .lake/build/lib/lean/PrismSplit.olean PrismSplit.lean
lake env lean -j1 -o .lake/build/lib/lean/PrismCounts.olean PrismCounts.lean
lake env lean -j1 -o .lake/build/lib/lean/PrismGeometry.olean PrismGeometry.lean
lake env lean -j1 PrismSeriesClosure.lean
```

The [macOS cache fallback](../../shared/lean/README.md) also applies. The serial check succeeded on Lean 4.19.0, commit `6caaee842e94`, with mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All three statements depend on `propext`, `Classical.choice`, and `Quot.sound`. The checked SHA-256 for `PrismSeriesClosure.lean` is `0474d85e47c9fe6072b54f69afb5732300d361b6bb43b31d5b11cf7b124d239d`. [Prerequisite source digests](lean/Geometry.md)
