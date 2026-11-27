# Finite paired-pole product audit

Lean source head `1be982dd72128c3cf1ee93c0af68cf800e3a21ab`. The SHA-256 of the hosted report is `117460e6a3915ec3e573030a1c1e8cab37f1f0a6342f562575d4870bc0943712`. [Successful hosted run and report](https://github.com/ProgramComputer/open-math-research/actions/runs/45968198860)

Lean checked and kernel-replayed twelve modules and audited 28 declarations. The six added declarations and the 22 earlier declarations report only `propext`, `Classical.choice`, and `Quot.sound`. [Earlier paired-profile source hashes](verification.md)

```text
Frozen upstream source 46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554
Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)
mathlib 0df444a360eaa60ab8c11dca51a86af692955474
Reused verified common-pin archive sha256=000f5b74d9fe3aa351b19b0db90b4ab23b1e6329cbe6f6129b355f68b285cc05
Compile CutoffFormalExp input-sha256=b6718e18865eb407f6b5a98a96e45f9adc4b2b196ea69dd79a0b29837e753911
Compile ExpAdd input-sha256=750ac2a79e905f9e194109dc80f6498ab6ddbfebd3d56ca43cee4da8de524939
Compile PairedExpProduct input-sha256=b6b6d10d895c410efc8dc01e59087d518526533cd386157b85aac76518638680
Compile RepositoryPairedProductLimit input-sha256=58ad9208c2ae824529065285857bda3d8601c680a2521906f35f3552d5e3b6fc
kernel_replay_exit=0 CutoffFormalExp
kernel_replay_exit=0 ExpAdd
kernel_replay_exit=0 PairedExpProduct
kernel_replay_exit=0 RepositoryPairedProductLimit
PASS: 28 paired-profile declarations audited
```

The actual permutation limit is `RepositoryQuotientAudit.tendsto_original_scaled_finite_paired_products`. It allows degree zero, positive degrees below the cutoff, and all larger degrees. The full distinguished-pole lattice resummation remains outside this check.
