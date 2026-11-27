# Full occupied-pole value audit

Lean source head `6fbc3d4682e491c73a7e921fb5d09fcf54c2ea72`. The SHA-256 of the hosted report is `08e75fae887804fc74aa418729713d0400e33a7031ebf7b5edaa64f117288a73`. [Successful hosted run and report](https://github.com/ProgramComputer/open-math-research/actions/runs/45970045290)

Lean compiled and kernel-replayed nineteen modules and audited 38 declarations. The ten added declarations and 28 earlier declarations report only `propext`, `Classical.choice`, and `Quot.sound`. [Earlier source hashes](product-verification.md)

```text
Frozen upstream source 46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554
Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)
mathlib 0df444a360eaa60ab8c11dca51a86af692955474
Reused verified common-pin archive sha256=000f5b74d9fe3aa351b19b0db90b4ab23b1e6329cbe6f6129b355f68b285cc05
Compile OccupiedSupportNet input-sha256=c89d3760a351784b833903f60291665d34748713b3845954090d337c590960ad
Compile OccupiedCoefficient input-sha256=1fc0666e094ef865e279bd99567049fcad822bb6e49fb82a7f98bc74f16538a7
Compile OccupiedExpansion input-sha256=3a8d03cfd8f046607f0e2ff4e95b19b0ef0c83f0ad49cbd59d1a2c1dc7879327
Compile ActualOccupiedValue input-sha256=ae0d1eac196261fbeb6344954e49b175c2a246a776d0ed335267b04087dc21ea
Compile ActualOccupiedLimit input-sha256=0c2e132aa39bdbf37139020fe767ffcc8c09990d26b32415c68366001b372b00
Compile OccupiedTuple input-sha256=9be22dae417ef4d60f04ac2357107978f1b13c4bdc54c72c66af20b0b246797d
Compile RepositoryOccupiedValue input-sha256=6b212ee930cd6403ef77d69ad1e29ebef05b2e656789eb282cbe046f0477d846
kernel_replay_exit=0 OccupiedSupportNet
kernel_replay_exit=0 OccupiedCoefficient
kernel_replay_exit=0 OccupiedExpansion
kernel_replay_exit=0 ActualOccupiedValue
kernel_replay_exit=0 ActualOccupiedLimit
kernel_replay_exit=0 OccupiedTuple
kernel_replay_exit=0 RepositoryOccupiedValue
PASS: 38 paired-profile declarations audited
```

The literal result is `RepositoryQuotientAudit.original_scaled_occupied_value` at positive coefficient degree and cutoff at least three. The bounded-aspect quantitative estimates and middle signs remain open Lean obligations.
