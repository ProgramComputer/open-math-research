# Exact finite two-cycle band

For every threshold $k\ge3$ and old size $n$ satisfying $2k\le n\le3k-2$ and
$n<192$, this calculation checks strict interlacing of the nonzero roots at
sizes $n$ and $n+1$. It tests the stronger statement that both signs of the
new-cycle term give the same strict sign as the derivative term at every old
root. The requested range contains 3,007 transitions and 379,502 old roots
counted with their reciprocal partners.

## Coefficients

Let $A_m$ be the Eulerian polynomial of degree $m-1$ for $m\ge1$. A cycle of
length $m$ has excedance polynomial $t A_{m-1}(t)$. In the band
$k\le n<3k$, the normalized polynomial is
$$
P_{n,k}(t)=A_{n-1}(t)
+t\sum_{a=k}^{n-k}\binom{n-1}{a-1}A_{a-1}(t)A_{n-a-1}(t).
$$
The length $a$ refers to the cycle containing label 1. Its other labels may
be selected in $\binom{n-1}{a-1}$ ways and the remaining labels form a single
cycle. Increasing relabelings preserve excedance counts on the two supports.

For old size $2k-1\le n\le3k-2$, the distinguished-cycle term is
$L(t)=\binom{n}{k-1}t A_{k-1}(t)A_{n-k}(t)$. The checker independently verifies
as an integer polynomial identity that
$$
P_{n+1,k}(t)
=t(1-t)P'_{n,k}(t)+(1+(n-1)t)P_{n,k}(t)+L(t).
$$
It tests $Q_+=P_{n+1,k}$ and $Q_-=P_{n+1,k}-2L$ against the same old polynomial.
Every row and pencil is checked to have the required degree, reciprocal
coefficients and extreme coefficients one. The Eulerian rows are reconstructed
from the integer recurrence and cross-checked with the finite-difference
formula for their coefficients.

## Exact signs and exhaustion

The checker starts with $A_1=1$. It builds lower-half Eulerian root brackets
by the same sign checks used for both pencils. For each threshold the first
two-cycle transition, from $2k-1$ to $2k$, supplies the seed brackets for the
requested band. Every subsequent old polynomial is the original row $Q_+$.
No input root archive is required.

At an old lower root of rank $h$ in order of increasing modulus, the old
endpoint signs are $(-1)^{h-1}$ and $(-1)^h$. On each old bracket the checker
tests both pencils for sign $(-1)^h$ at both endpoints. It bisects the old
sign change with integers when either pencil endpoint has the wrong sign.
Each endpoint is a dyadic with denominator $2^{256}$. A fixed-point Horner
calculation certifies the sign using a strict integer error bound. Each
rounding has magnitude less than one scaled unit and all subsequent Horner
multiplications contract its error. The degree therefore bounds the total
error in scaled units. The checker increases the Horner scale if needed
and treats the endpoints $0$ and $-1$ exactly.

For each pencil the endpoint signs force one lower root between zero and
the first old bracket and one in each gap between old brackets. If the old
degree is odd, its center $-1$ supplies the correct sign for another new
root between the last lower old bracket and $-1$. If the pencil degree is
odd, reciprocity gives its simple center. The lower roots, reciprocal
partners, and center where required exhaust the degree. The two pencils
thus keep sign $(-1)^h$ throughout every old lower bracket. The same
sign conclusion at the other old roots follows from reciprocity and the
explicit central check. At an old root of rank $h$, that sign is the sign
of $t(1-t)P'_{n,k}(t)$. Therefore
$|L(t)|<|t(1-t)P'_{n,k}(t)|$ at every old root. The positive pencil proves
strict consecutive interlacing throughout the range.

## Replay

Run with Python 3 and python-flint installed. FLINT is used only for integer
polynomial arithmetic. Root signs use Python integers.

~~~sh
python3 -I -O verify_two_cycle_band.py --records replay.jsonl.gz
cmp replay.jsonl.gz two-cycle-pairs.jsonl.gz
python3 -I -O verify_two_cycle_coefficients.py
~~~

The certificate index holds 3,007 transitions and 379,502 old roots including reciprocal partners. Its compressed SHA-256 is `314ac535c7e3d7dbc2bb4b78e701950bfee860145f51d3a452ad4d5f988abfed`. [Index](two-cycle-pairs.jsonl.gz) · [Root checker](verify_two_cycle_band.py) · [Independent coefficient reconstruction](verify_two_cycle_coefficients.py)

The output gives the count and deterministic dyadic-bracket digest for each
threshold. The optional gzip JSONL index retains each $(n,k)$ check outcome
and hashes the coefficient vectors and interval endpoints. Use
`--full-records` to retain those vectors and endpoints in the stream as well.
Bracket endpoints are integer moduli scaled by $2^{256}$. Each hash is SHA-256
of the corresponding compact ASCII JSON array. [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)
