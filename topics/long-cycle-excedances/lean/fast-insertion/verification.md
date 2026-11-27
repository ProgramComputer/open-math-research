# Exact checkpoint route verification

The exact route checks the arithmetic for the 26 first-pair brackets at cutoff 13. Its source-to-permutation connection through the specialized recurrence remains pending on this route. The separate packed route already verifies the same signs as part of a larger 524-sign slice. [Packed slice](https://github.com/ProgramComputer/open-math-research/pull/264)

The producer compiled and replayed all 70 arithmetic checkpoint modules across three groups. The initial endpoint audit compiled and replayed the checkpoint aggregate. After the first final process was interrupted, the split endpoint run compiled and replayed all nine first-pair modules below. The separate checkpoint aggregate proves exact table agreement conditional on its model. The nine split modules check the literal Eulerian weight equality, the five blocks of endpoint arithmetic, their aggregate and the rank list. [Arithmetic producer](https://github.com/ProgramComputer/open-math-research/actions/runs/45930417212) · [Split audit](https://github.com/ProgramComputer/open-math-research/actions/runs/45941917280)

| Split module | Source SHA-256 | Object SHA-256 |
| --- | --- | --- |
| `FirstPairArithmetic` | `4a2e10a8a0f3a550bdb03e858e9940033bd06817077c1afa8934915069f08932` | `511b8b1b092b121f4218ddcaee422f2bca03d8534672bdc1933a380237361943` |
| `FirstPairChecks` | `5fef61a1107c68b1510d5f8945a15d6729f7b8230cf06f24684bb414db9b6bce` | `51cb7db5344e98d575be60e761ae016650259961e234a1d5d74fd1f98c1dc075` |
| `FirstPairChecks0` | `55df87be3fbdd77709213fc31d82c3c47d3e8edb5fef78c9ba8f91bf44665e40` | `1fbcf87c9a02850890ff287b6dcd305911c7b3fd82b62309918988cafb12d6a8` |
| `FirstPairChecks12` | `4e9d85cf4a4073e468c2537bfd5fcd8e038d2a2ec765c502a0f03f8b96e30d72` | `acc431a3b83b295e5c7baf08a0fa56d069d5af185dbc20dd26d5b53acc9a0006` |
| `FirstPairChecks18` | `7fb4d19aec6ce8b7e9230876a4e884689e396fc441bc113ba4bc4a00c33270e7` | `0343f77f90902a73d3175d862bca26ddabb9c60686151d6b2b72940db0179303` |
| `FirstPairChecks24` | `a1452c80b81aa7dcbb65b003436467318b67058e65ec413beb5952f1b3106d3f` | `3460d092b24e32171d11be5b44b8ca1ab744e27859ead0b14cb67ea7a3e62c95` |
| `FirstPairChecks6` | `9134291f4c32b9309351513e6700c44f66051050424710d1a372492100234be7` | `8f18f906f80f5ca39ad8342390bfad75c629ecba03f6dfceae7d3cc2f49f8d5d` |
| `FirstPairEulerian` | `09dcee7d5a448e655b73d29f2714b1b6f2afc2f8e095164b5965f1b1fd059fed` | `6b2aed4d6b44d8645042bb64464ae1fa09ceced1900f3abf7aa7c2c0727ea143` |
| `FirstPairWeights` | `9ac84c0253d81cd9e631094dcb42073ddd571306000ef18afcc43c75a59e2de4` | `f4b96b4ebbe34059a0041892ecb215416eff7eb011f825923994559f44bf266f` |

The final run at `fae2a768e94780864c4362f0962dc5bd541d2a25` authenticated and recovered the three arithmetic groups and all nine endpoint objects. I compared the nine objects and their producer receipts byte for byte between the producing and recovered bundles. The compiler is Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and Mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`. [Successful-leaf producer bundle](https://github.com/ProgramComputer/open-math-research/actions/runs/45941917280/artifacts/15173224004) · [Recovered bundle](https://github.com/ProgramComputer/open-math-research/actions/runs/45943242262/artifacts/15174265638)

The isolated compilation of the explicit cutoff-13 recurrence was stopped by the resident-memory watchdog after it reached 12,369,051,648 bytes against the 12,348,223,488-byte limit. The remaining model field is the specialization of the supplying insertion recurrence to the literal cutoff-13 enumerator and the Eulerian polynomial of order 12. The upstream general recurrence compiled and replayed. The audit did not reach the final model and sign declarations. The repeated resource failure motivates pausing the exact route until a distinct compilation strategy is available. [Final run](https://github.com/ProgramComputer/open-math-research/actions/runs/45943242262/job/140322153791) · [Authenticated diagnostic bundle](https://github.com/ProgramComputer/open-math-research/actions/runs/45943242262/artifacts/15173509801)

The producing bundle SHA-256 is `e3aa4ee98052400944a2376317131425a37df1579d155ecf25f81b87cb3998fd`. The recovered bundle SHA-256 is `93a5f4da139bbfbaf92f4d98197ab9ac911be433dac5f8d31da9dc4364df6319`. The diagnostic bundle SHA-256 is `08cdd84594330bf302a242afee6cec46d8f0b12d504eb65e29a1c9a3e7faa7ee`.

~~~text
kernel_replay_exit=0 CheckpointReplay
Compile FirstPairRecurrence sha256=345dc1b797be94b3b19aab04ed2ae401450893b22e56a0dad7083adc87e94397
RuntimeError: compile FirstPairRecurrence reached 12369051648 resident bytes (cap 12348223488)
~~~

To reproduce the complete source attempt, use the pinned Linux toolchain and the [driver command](README.md#verification). With no cached objects, the driver regenerates and checks the exact checkpoints. The workflow permits reuse of the pinned, authenticated producing artifacts and applies the same strict build and kernel replay checks to each new module.
