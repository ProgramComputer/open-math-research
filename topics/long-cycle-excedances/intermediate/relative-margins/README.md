# Sharp dyadic coefficient tolerance for the archived signs

Let $P=E_{N,k}/X$ be the reduced excedance polynomial in a record of the [intermediate witness archive](../witness-ledger/README.md). Write $y$ for an endpoint modulus and $\sigma$ for the sign prescribed for that row at $-y$. Across all 2,164,796 row, endpoint and sign choices, exact arithmetic gives

$$
\sigma P(-y)>2^{-32}P(y).
$$

The exponent 32 is sharp among integer exponents. At cutoff 13 take the upper row $N=256$ and the left endpoint of rank 32 in the pair with old size 255. Here $y=871689497096755307205496065384395168305363817049/2^{170}$ and $\sigma=1$. Evaluation with all 255 coefficients gives

$$
2^{31}P(-y) < P(y) < 2^{32}P(-y).
$$

**Meaning for coefficient errors.** Write $c_j$ for the coefficients of $P$. If each coefficient of a real polynomial $Q$ differs from $c_j$ by at most $\varepsilon c_j$, the triangle inequality gives $|Q(-y)-P(-y)|\le\varepsilon P(y)$. Thus all prescribed signs survive arbitrary simultaneous relative changes of size at most $2^{-32}$. At the displayed point the polynomial $Q(X)=P(X)-\sigma\varepsilon P(-X)$ attains the error in the adverse direction. At $\varepsilon=2^{-31}$ its prescribed sign reverses. This exponent concerns the archived evaluations with endpoints held fixed. It gives a precision target for compressed verification of the interlacing proof.

## Verification

The unrounded test uses the first 60 exact coefficients, signed floor Horner $H$, positive ceiling Horner $A$, and an upper bound $T$ on the absolute omitted tail at either sign of the argument. Since $0<y<1/2$, the floor errors have sum of absolute contributions below 2. It suffices to check

$$
2^{32}(\sigma H-2)-A>(2^{32}+1)T.
$$

The GMP test passed every comparison. It used the sharp rational tail 29 times. The independent reviewer reproduced these counts and evaluated the sharpness witness using the full polynomial. [Integer test](../integer-signs/signs.cpp) · [Independent review](independent-review.md) · [Full-degree witness verifier](check-sharpness.py)

The second test uses coefficients rounded down to 48 significant bits during the insertion recurrence. The [proved enclosure](../../lean/compact-rows/README.md) puts the exact coefficients between the decoded values and those values times $1+2^{-36}$. Directed dyadic arithmetic with 60 significant bits bounds the positive and negative parts of the signed prefix separately. It subtracts an upper bound on $2^{-32}$ times the positive prefix from the resulting lower bound. A positive result $m$ certifies this lower margin. An inconclusive subtraction returns zero and fails the test.

For $W=60$, set $u=(W+1)^N$ and $v=(W+2)^N$. The positive coefficient majorant gives $T\le u^2y^W/(u-yv)$ whenever $u>yv$. The test compares a lower bound on the left with an upper bound on the right of

$$
m u>(1+2^{-32})u^2y^W+m yv .
$$

Passing establishes both $u>yv$ and the required strict relative margin. The checker passed at every endpoint. The directed operations use integer significands with products at most 120 bits. GMP handles the row recurrence and conversion of the inputs. [Directed arithmetic](../integer-signs/relative-dyadics.hpp) · [Exact rational regression tests](check-dyadics.cpp) · [Execution record](verification.txt)

**Formal coverage.** On the [shared research pin](../../../../shared/lean/README.md), Lean 4.19.0 checks sign preservation and the extremal perturbation for an arbitrary real polynomial under the stated hypotheses. The finite margin comparisons and sharpness witness are executable exact arithmetic outside Lean. [Formal statements and proofs](RelativeRootMargin.lean)

## Reproduce

From this directory in a full research checkout, with a C++17 compiler supporting unsigned 128-bit integers, GMP and Python 3, run

~~~sh
c++ -std=c++17 -O3 -Wall -Wextra ../integer-signs/signs.cpp -lgmpxx -lgmp -o /tmp/long-cycle-signs
python3 -B ../integer-signs/run.py ../witness-ledger/shards /tmp/long-cycle-signs --relative-32
python3 -B ../integer-signs/run.py ../witness-ledger/shards /tmp/long-cycle-signs --relative-32-dyadic
python3 -B check-sharpness.py ../witness-ledger/shards
c++ -std=c++17 -O2 check-dyadics.cpp -lgmpxx -lgmp -o /tmp/check-directed
/tmp/check-directed
(cd ../../../../shared/lean && lake env lean -DwarningAsError=true ../../topics/long-cycle-excedances/intermediate/relative-margins/RelativeRootMargin.lean)
~~~

Each archive run checks the ordered uncompressed byte count and SHA-256. The existing [integer-sign instructions](../integer-signs/README.md) give the independent distinguished-cycle replay of the first pair.
