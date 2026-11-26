# Effective real-rootedness sectors for balanced arrays

For every row count and every dimension $`d\ge2`$ with $`4d\ge n`$, the balanced-array polynomial has all simple negative roots if the cap satisfies $`10r\ge9d`$. Its degree is $`\lfloor nr/d\rfloor`$. The coefficient sequence is the one in [Per Alexandersson’s conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays).

Two further effective guarantees hold.

- For rational $`1/2<\rho<1`$ and $`c>\rho(1-\rho)\log4`$, a computable row cutoff suffices when $`d\ge cn`$ and $`r\ge\rho d`$.
- If $`\log n\ge64`$, $`d\ge4n/\log n`$ and $`4n(d-r)\le d^2`$, every root is simple and negative. At the other cap endpoint, $`4nr\le d^2`$ gives ordinary coefficient separation.

For the all-row theorem, the [finite result through 35 rows](../finite-residual/README.md) handles the initial range. The [exact interval sweep and refinement](sector-finite.md) cover 36 through 1023 rows, and the [analytic proof](sector-proof.md) covers all larger rows and gives the general effective sector. The [sublinear proof](sector-logarithmic.md) gives the explicit logarithmic threshold. [Independent agent-assisted review](independent-sector-review.md) · [Sources and prior results](literature.md) · [Manuscript](paper.tex)

**Formal verification**　⬜ None. The finite certificate uses exact directed integer arithmetic and a separately reproduced binary64 sweep.

## Replay

Run from this directory with Python 3 and a C++17 compiler with unsigned 128-bit integer support. Temporary outputs go to a separate directory. The pinned refinement helper is already reviewed and supplies the overloaded-row histogram recurrence.

~~~sh
work=$(mktemp -d)
revision=114696f2f69429411c6cd4f11955aee963d5320d
git cat-file -e "$revision^{commit}" || git fetch origin "$revision"
git show "$revision:topics/balanced-arrays/curvature-compensation/defect-histogram.py" > "$work/counter.py"
python3 -B sector-constants.py
c++ -std=c++17 -O3 sector-finite-integer.cpp -o "$work/sector"
"$work/sector" 36 1023 > "$work/misses90"
"$work/sector" 36 1023 9 10 1 > "$work/misses91"
"$work/sector" 36 1023 19 20 > "$work/misses95"
cmp "$work/misses90" sector-finite-integer-fail90.txt
test ! -s "$work/misses91" && test ! -s "$work/misses95"
python3 -B sector-finite-refine.py "$work/misses90" --counter "$work/counter.py" > "$work/refined"
cmp "$work/refined" sector-finite-integer-refine90.txt
~~~

For the separately reproduced binary64 sweep use `c++ -std=c++17 -O3 -ffp-contract=off -fno-fast-math sector-finite.cpp` on a binary64 target with no excess precision and run the same three input ranges. The [90% replay](sector-finite-integer-run90.txt), [offset-one replay](sector-finite-integer-run90-plus1.txt), [95% replay](sector-finite-integer-run95.txt), and [exact refinement replay](sector-finite-integer-run-refine90.txt) record the counts.

The original all-cap, all-row conjecture remains open.
