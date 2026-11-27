# Exact linear-table pinned audit

Lean source head `2efea388f758f540e9f356dc63d63a5f8792d366`. The hosted proof-log SHA-256 is `0a644f1d3ba597d31ab4763b28b5da238b7b97431b3ceed4de559079eb59490a` and the Lean executable table SHA-256 is `a0df998c4f2c700d795dccd8b6681a7f3c7e03ecdb48335627707001bf30b701`. [Successful hosted run](https://github.com/ProgramComputer/open-math-research/actions/runs/45982833370)

The pinned driver matched 41 source hashes, 16 kernel replays and 35 designated axiom reports. The six added declarations, including `original_slab_linear_envelope`, reported only `propext`, `Classical.choice`, and `Quot.sound`. No evaluation axiom enters the theorem. The independent executable comparison checks all 2,169 entries against the existing exact Python table.

```text
Frozen upstream source 46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554
Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)
mathlib 0df444a360eaa60ab8c11dca51a86af692955474
Reused verified common-pin archive sha256=000f5b74d9fe3aa351b19b0db90b4ab23b1e6329cbe6f6129b355f68b285cc05
Compile LiteralLinearTable input-sha256=2087f9ffb6dd3c5281bd2c0c532610c590b8ae01f2c80da74800ffe04a5d46ba
Compile LinearSlabs input-sha256=3ce57f25b613267705e53e0f24d4580980a201fe9718e2ac5f53e1248f9b3136
kernel_replay_exit=0 LinearSlabs
kernel_replay_exit=0 LiteralLinearTable
PASS: 35 marked-bin declarations audited
```

The result supplies the linear table inequality for all bins and finite pole sets in each slab. The remaining quantitative determinant inputs and original interlacing theorem lie outside this audit.
