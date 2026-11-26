# Four balanced columns with row cap two

**Theorem.** For every integer $n\ge0$, let $P_n(q)=\sum_k a_{n,k}q^k$, where $a_{n,k}$ counts labeled binary $n\times4$ arrays in which every column sums to $k$ and every row sums to at most two. Then $P_n$ has exactly $\lfloor n/2\rfloor$ distinct negative zeros. For $n=0,1$ it equals 1.

This is the unit-weight $U_{2,4}$ case of Per Alexandersson’s balanced-array conjecture. The full conjecture for arbitrary rank and number of columns remains open. Consecutive interlacing is a separate question. [SymCat conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays) · [Alexandersson’s statement](https://github.com/PerAlexandersson/RealRooted/issues/2005) · [Literature and priority record](literature.md)

- [Proof](proof.md) and [manuscript source](paper.tex) give the direct degree, finite verification through $n=532$, and the uniform sign argument from $n=533$ onward.
- [Central](central.md), [small-parameter](small.md), and [upper](upper.md) estimates give the bounds used in the sign argument.
- [Lower certificates](certificates/lower.jsonl) handle the first 40 sign changes for every $n\ge533$. The [finite certificates](certificates/rows/) contain all coefficient rows and dyadic test points for $0\le n\le532$.
- Independent agent-assisted reviews cover the [analytic estimates and phase join](review/analytic.md) and the [finite prefix](review/prefix.md). A fresh [blind agent-assisted review](review/blind.md) checked the assembled all-$n$ argument against the original conjecture and found no substantive gap.
- **Formal verification ⬜ None.** There is no checked Lean or Rocq proof. The certificate scripts use exact integers and rigorous Arb intervals.

## Replay

From this folder, use Python 3 with [python-flint 0.9.0](https://pypi.org/project/python-flint/0.9.0/). The code for the small-parameter and upper constants uses only the standard library.

~~~sh
python -m pip install python-flint==0.9.0
shasum -a 256 -c SHA256SUMS
python code/small_constants.py
python code/upper_constants.py
python code/middle.py
set -o pipefail
python code/lower.py 533 $(seq 1 40) | diff -u certificates/lower.jsonl -
python code/prefix.py --directory certificates/rows --verify --last 532
python code/independent_prefix.py certificates/rows --last 532
~~~

The compact interval replay checks 2,048 cells and gives an error bound of $33827/100000$. The phase join checks 64 cells. The lower replay verifies the 40 shifted integer polynomial sign certificates. The independent finite replay reconstructs 71,289 coefficients and verifies 70,225 interior signs by integer arithmetic.
