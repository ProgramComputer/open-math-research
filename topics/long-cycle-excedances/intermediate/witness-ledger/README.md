# Coefficient-free finite interlacing witnesses

The ledger gives the separating points accepted by the independent intermediate sign checker for Alexandersson's minimum-cycle-length excedance conjecture. A record is the ASCII/UTF-8 line `n,k,rank,a_num,a_bits,b_num,b_bits` with LF terminator and no header. Decimal fields are nonnegative integers without leading zeros. An endpoint is `num / 2^bits`. The numerators are positive and odd. Rows are emitted in increasing cutoff, old size, and angular gap rank. Adjacent brackets in the same pair must be strictly separated.

The upstream checker is the file `topics/long-cycle-excedances/intermediate/cross-check/verify.py` from research commit `97efaa5c1671e760d846194b7aecaa080555792d`, Git blob `bf8a2f6dea448941b96e5f13277c04ee6dfb9217`, SHA-256 `d0e7dbb6a18e5c6734fda1e1cde61f56c609e1cf87a509cab7824f0b431ffdd0`. [Upstream source](https://github.com/ProgramComputer/open-math-research/blob/97efaa5c1671e760d846194b7aecaa080555792d/topics/long-cycle-excedances/intermediate/cross-check/verify.py) · [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances)

- `export.py` verifies the upstream file hash and adds one emitter immediately after the upstream bracket acceptance tests. FLINT produces exact binary floating-point endpoints. The emitter uses their exact mantissas and exponents, with zero decimal rounding. It sends existing diagnostics to stderr.
- `metadata.py` verifies every expected key, structure, uniqueness, endpoint range and exact bracket order. It does not import FLINT or the upstream checker. For each admissible pair it calculates the expected ranks independently, starting at the exact exterior integer and taking the first sample satisfying both high-angle entrance inequalities. It uses Machin's formula with alternating arctangent bounds for π, then exact alternating Taylor bounds for sine and monotonicity on the first quadrant. For each candidate before the entrance it proves at least one inequality fails. At the entrance it proves both hold. Impossible-to-decide cases fail the verifier. Pairs with no intermediate gaps are included in the counts. Omissions, duplicates and extra records fail strict matching against the expected ordered stream.
- `WitnessLedger.lean` defines exact natural-number cross multiplication for dyadic order. Its soundness theorem proves agreement with the supplied rank list, absence of repeated keys, rational bounds $`0<a<b<1`$, and $`b<a'`$ for consecutive brackets in the same pair. `lean_fixture.py` generates a literal test from a ledger and computes the expected list independently through `metadata.py`. The included `CheckedShard.lean` uses ordinary `by decide`.

## Reproduction

Run the exporter using Python with `python-flint==0.9.0`, and run the independent metadata verifier with ordinary Python. For the stored genuine shard:

~~~sh
python3 -B export.py ../cross-check/verify.py --nmax 255 --kmin 13 --kmax 13 > shard.csv
python3 -B metadata.py --nmax 255 --kmin 13 --kmax 13 < shard.csv
python3 -B lean_fixture.py shard.csv --nmin 251 --nmax 255 --kmin 13 --kmax 13 > CheckedShard.lean
# Run the next command from the repository’s shared/lean directory.
lake env lean /absolute/path/to/topics/long-cycle-excedances/intermediate/witness-ledger/CheckedShard.lean
~~~

The full range needs no large checkout or resident ledger. Use a pipeline with failure propagation enabled:

~~~sh
set -o pipefail
python3 -B export.py ../cross-check/verify.py 2> full-export.progress | python3 -B metadata.py
~~~

The 22 supplied gzip shards contain the exact full stream in 29,013,737 compressed bytes. The largest shard is 1,391,016 bytes. Their [manifest](shards/manifest.json) lists every file and the SHA-256 of the records for each of the 244 cutoff values, including cutoffs with no intermediate gaps. Decompress and authenticate the full stream without putting it on disk.

~~~sh
set -o pipefail
python3 -B verify_archive.py shards --emit | python3 -B metadata.py
~~~

Rebuild the compressed archive with `python3 -B archive.py /path/to/new-directory` as the consumer of the exporter stream. The archive uses gzip with a zero timestamp and splits before a shard would exceed 3,000,000 uncompressed bytes. Per-shard compression checks are distinct from the canonical uncompressed digest.

## Checks and scope

The full streaming run exited successfully. The exporter and independent metadata totals agree on 93,902 pairs, 82,395 nonempty pairs, 541,199 gaps and highest entrance 33. The exact CSV size is 63,014,205 bytes, the largest denominator exponent is 283, and the stream SHA-256 is `8f8115d4f203840560dd74f7cf12654d0bca00561c8ff473f27ed6af3f20a73e`. No full CSV was stored. The full exporter and metadata verifier completed in about 170 seconds on the local arm64 host. [Machine-readable receipt](full-metadata.json) · [Exporter diagnostics](full-export.progress)

The $`k=13`$ shard at sizes 251–255 has 5 pairs and 131 gaps, occupies 15,226 bytes as CSV and 7,514 bytes with reproducible gzip, and has SHA-256 `e6b756647fcde23d8047abf9968340c6787f22a62cba54d59b3a917e43c628d0`. A fresh export reproduced those bytes. A separate 320-bit interval check placed all 131 shard brackets strictly inside their stated angular gaps. The independent verifier rejected seven mutations covering missing, duplicate, swapped and extra records, reversed endpoints, same-pair overlap and noncanonical decimal encoding.

The local proof and generated shard passed Lean 4.19.0 build commit `6caaee842e94` with mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. `dyadicLT_sound` and `check_sound` have only `propext`, `Classical.choice` and `Quot.sound`. The literal `checkedShard` proof has only `propext`. [Build and axiom output](lean-replay.txt)

The exporter preserves the existing checked numerical inequalities. The independent verifier checks witness metadata. The Lean checker establishes order and uniqueness for a supplied expected-key list. The formal connection of that list to the analytic angular entrances remains outstanding. The first sign obligation is to connect the four exact endpoint signs for each gap to the genuine old and new polynomials via the verified coefficient oracle and a formally checked remainder bound. The full sign replay and its joins to the exterior, middle and high-angle arguments are still required for an end-to-end Lean proof.
