# Faster kernel checks for packed long-cycle rows

[The shift checker](FastPackedPoint.lean) computes the signed floor and positive ceiling Horner values in one walk over the packed row. It evaluates dyadic division by exact signed right shifts. It tests a geometric tail using an outward power-of-two radius, which each check verifies against the endpoint. The checker is proved equivalent to the coarse integer comparison. A successful coarse comparison implies the original sharp check and hence the strict sign of the original unweighted excedance quotient, given the rounded row identification. The sharp check remains available for endpoints where the coarse comparison is inconclusive. [Original quotient transfer](RepositoryFastPackedPoint.lean) · [Coarse tail proof](CoarseCheck.lean)

[The size-1,000 sample](HighSizeAudit.lean) checks 80 endpoint signs at cutoff 51 and eight at cutoff 160. Each cutoff uses every archived gap for that old size, with signs for the old size 1,000 and the next size 1,001. The two exported sign theorems take the exact identification of the sampled packed coefficients with the rounded recurrence as a premise. The generator supplies those coefficients by recurrence, and authenticates the archived endpoints against the full canonical stream. Kernel certification of the two large recurrence tables is outside this benchmark. [Sample definitions and premises](HighSizePoint.lean) · [Generator](generate.py)

[The storage proof](RowWordStorage.lean) packs the 64-bit words of a row into one natural number. It proves that decoding at the original length exactly recovers any list of words below $2^{64}$. The benchmark generates the same 244 rows in both forms, checks all 244 round-trips in Python, then checks the quotient recurrence seed and final step in both layouts in Lean. The final step produces the size-256 row. [Storage control](StorageAudit.lean)

## Replay and measurements

From the root of the repository, with Lean 4.33.1 available on the path, run the existing common-pin setup and the benchmark together.

```sh
ulimit -Sn 65536
python3 -Bu topics/long-cycle-excedances/lean/fast-packed-checks/check.py /tmp/long-cycle-fast-packed-checks
```

The driver pins mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`. Its optional second argument is the authenticated import archive used by the common-pin check. The driver reports source hashes, axiom checks, kernel replay status, wall time for compilation and replay together, and source and object sizes. The sharp and coarse controls use the same archived endpoints and the same rounded words. [Hosted workflow](../../../../.github/workflows/long-cycle-fast-packed-checks.yml)

On a local Lean 4.19.0 prototype, the 80-sign cutoff-51 sample took 31.93 seconds to compile with the sharp checker and 9.57 seconds with the paired shift checker. The eight-sign cutoff-160 sample took 3.74 and 2.31 seconds. The cutoff-13 storage prototype reduced the 244-row object from 11,293,528 bytes to 1,073,888 bytes. The replay above measures the checked package on the common pin and includes kernel replay in its times.

The full archive contains 541,199 gaps, 2,164,796 signs, and 153,082 rounded recurrence transitions across 187 active cutoffs. Scaling the original cutoff-13 shard’s observed per-unit cost to these counts gives 40.7 row worker-hours and 91.1 endpoint worker-hours. These are planning estimates based on the small shard. Larger sizes, a wider prefix, and runner setup can change the cost. The paired shift and storage comparisons here test two components of that cost on fixed real inputs.
