# Dyadic windows for cutoff eight

At cutoff $k=8$, the certificate brackets every zero of the reduced row in $(-1,0)$ for each size $32\le n\le250$. It also gives the sign of the successor row at each endpoint and, for odd $n$, at $-1$. The 219 consecutive pairs contribute 15,166 windows and 60,773 strict signs. This is a finite exact-arithmetic check. The supplied data are in the variable of the [formal half-axis theorem](../../lean/common-pin/RepositoryHalfAxisAssembly.lean).

Write $P_n(t)=E_{n,8}(t)/t$ for the strict-excedance polynomial after removing the common zero. Each line of the compressed file is a JSON array $[n,i,a,e,b,f]$. Set $l=a/2^e$ and $u=b/2^f$. For fixed $n$ the records start at $i=0$, occur in increasing order and satisfy $0<l_i<u_i<l_{i+1}<1$ wherever both windows exist. The signs at $-l_i$ and $-u_i$ are $(-1)^i$ and $(-1)^{i+1}$ for $P_n$, and $(-1)^{i+1}$ at both points for $P_{n+1}$. For odd $n$, the sign of $P_{n+1}(-1)$ is $(-1)^{\lfloor(n-2)/2\rfloor+1}$.

These signs give a root of the successor in each gap between successive old windows. Its constant term gives the first sign at zero. At odd size the extra central sign supplies the last gap. Reciprocity gives the other half of each root list, with a central root at $-1$ for a row of odd degree. The degree count gives simplicity and excludes additional roots. The finite-prefix proof already established these cases in the gamma variable. The purpose of this data set is direct input to the formal half-axis theorem. [Finite-prefix proof](../README.md) · [Certificate](k8-n32-250.jsonl.gz)

## Reproduction

Run the following commands in this directory. Both scripts use Python and python-flint 0.9.0. The generator counts by permutation insertion, then searches and shortens dyadic windows using directed integer Horner bounds. The verifier counts independently by the cycle containing label 1 and uses FLINT rational polynomial evaluation at every supplied endpoint. It also checks the degrees, reciprocity, indices, endpoint order and central signs.

~~~sh
uv run --no-project --with python-flint==0.9.0 python -I verify.py k8-n32-250.jsonl.gz 8 32 250
uv run --no-project --with python-flint==0.9.0 python -I generate.py rebuilt.jsonl.gz 8 32 250
uv run --no-project --with python-flint==0.9.0 python -I verify.py rebuilt.jsonl.gz 8 32 250
~~~

Both scripts report the SHA-256 of the uncompressed JSON lines, `95f445fa4e7864984c33ca44eb2f83a8295a628721e0b65bf523fb55265490e8`. The largest endpoint numerator uses 25 bits and the largest denominator is $2^{250}$. Lean coverage of these particular certificate records is pending.
