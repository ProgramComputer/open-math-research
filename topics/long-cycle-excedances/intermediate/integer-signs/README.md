# Exact integer signs at the intermediate witnesses

The GMP checker certifies the actual signs at both dyadic endpoints of every gap in the [witness archive](../witness-ledger/README.md). It reconstructs the first 60 coefficients of both original reduced permutation rows using largest-label insertion. In each gap the old row changes sign, and the new row has the opposite sign from the old left endpoint at both points. The full stream contains 541,199 gaps spanning 82,395 nonempty consecutive pairs. The run checks 2,164,796 strict signs. This is exact computational verification. A Lean replay of the full sign archive and the analytic joins remain outstanding. [Full replay output](full.log) · [Independent audit and rebuild](independent-review.md) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)

The canonical decompressed stream is 63,014,205 bytes with SHA-256 `8f8115d4f203840560dd74f7cf12654d0bca00561c8ff473f27ed6af3f20a73e`. The runner verifies both values unconditionally. It streams the archive and creates no decompressed ledger file. The C++ parser independently requires seven canonical integer fields and bounds the dyadic exponents. It checks increasing record keys, contiguous ranks within each pair and strict endpoint order. The preceding [metadata verification](../witness-ledger/README.md) establishes completeness and the rank range.

## Exact arithmetic

For row size $`N`$, the coefficient bound is $`c_i\le(i+1)^N`$. Let $`W=60`$, let $`y=p/D`$ with $`D=2^b`$ and $`0\lt y\lt1/2`$, and evaluate the retained polynomial at $`-y`$. The integer Horner update is $`c_i-\lfloor yh\rfloor`$ when the previous approximation is $`h`$. Taking a floor incurs error of absolute value less than one at each step. Prior error contracts by the factor $`y`$, so the total error is below $`1/(1-y)\lt2`$. For direction $`\sigma\in\{-1,1\}`$, the rounded signed result minus two is a strict lower bound $`M`$ for the signed retained value.

Put $`u=(W+1)^N`$ and $`v=(W+2)^N`$. The first omitted monomial has absolute value at most $`u y^W`$, and the majorant tail has successive ratios at most $`yv/u`$. The checker uses these integer comparisons.

- Let $`s=b-\mathrm{bitlength}(p)`$. Then $`y\lt 2^{-s}`$. If $`2^s u\ge2v`$, the ratio is below one half. The tail is then below $`2u\,2^{-sW}`$. For $`M\gt0`$, the comparison $`2^{sW} M\gt2u`$ certifies the sign.
- Otherwise the sharper comparison uses $`U=Du-pv\gt0`$. The geometric bound is $`u^2p^W/(D^{W-1}U)`$. If $`M\gt0`$ and $`M D^{W-1}U\gt u^2p^W`$, the sign is certified without constructing the exact retained value.
- If the rounded lower bound is insufficient, the checker computes the homogeneous numerator $`S=\sum_{i=0}^{W-1}c_i(-p)^iD^{W-1-i}`$ exactly and tests $`\sigma S U\gt u^2p^W`$.

The full replay used the sharper tail 28 times and did not need the exact retained numerator fallback. Each branch checks the same strict sign with a certified tail bound. [C++ checker](signs.cpp) · [Archive runner](run.py)

## Reproduce

From this directory, with a C++17 compiler and GMP's C++ development library installed, run:

~~~sh
c++ -std=c++17 -O3 -Wall -Wextra signs.cpp -lgmpxx -lgmp -o /tmp/long-cycle-signs
python3 -B run.py ../witness-ledger/shards /tmp/long-cycle-signs
~~~

If your GMP installation is outside the default compiler search path, supply its include and library directories with `-I` and `-L`.

The independent reconstruction uses `python-flint==0.9.0`. It counts the support of the cycle containing the least label, computes Eulerian coefficients from alternating power sums, and compares its reduced coefficients with both the recorded fixture and the insertion checker. The two arrays contain 120 coefficients with SHA-256 `5458f69b072a2f16ca975e4836bd4cd2e0b0b1b7626dadd7e5fa21398c0daa2e`. The reconstruction uses homogeneous integer evaluation at all four signs in each of the first pair's 26 gaps. [Fixture](first-pair-coefficients.jsonl) · [Independent output](first-pair-output.txt)

~~~sh
python3 -B reconstruct.py ../witness-ledger/shards/part-01.csv.gz /tmp/long-cycle-signs
~~~
