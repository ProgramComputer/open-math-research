# Verification of the bounded-aspect original interlacing theorem

The hosted composition check passed on `1100cd5daa44bccfb5e6d69730945bab45bb7206`. It used Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, mathlib at `0df444a360eaa60ab8c11dca51a86af692955474`, and frozen upstream sources at `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554`. The authenticated shared object archive has SHA-256 `000f5b74d9fe3aa351b19b0db90b4ab23b1e6329cbe6f6129b355f68b285cc05`. [Hosted job](https://github.com/ProgramComputer/open-math-research/actions/runs/46004401561/job/140523806504) · [Pinned source and manifest checker](../pinned-quotient/check.py)

The checked declaration `RepositoryQuotientAudit.original_bounded_aspect_interlacing` applies to the original permutation enumerators at successive sizes $n$ and $n+1$ when $n\ge10000$, $2\le k$, and $4k\le n\le48k$. It gives `StrictNegativeInterlacing` for the quotients by their common zero, with old degree $n-2$, and `WeakRealInterlacing` for the original rows. The proof uses the finite and strict adjacent determinant bound for this range, the ordered exterior and angular witnesses and the exact reciprocal root assembly. [Literal Lean theorem](RepositoryBoundedInterlacing.lean) · [Statement and proof outline](README.md)

The build compiled 299 repository modules in import order, with 9 explicit frozen-source compiles. The source and compiler-input SHA-256 reports were checked against the exact Git objects and the authenticated upstream sources. The four common-pin compatibility ports produce the same checked bytes as the exterior audit. The composition also renames the vertical `cutoffExp` identifier to `verticalCutoffExp` in two source-checked modules to distinguish it from the paired power-series definition. Reversing this token replacement recovers both original files byte-for-byte. The six new proof modules replayed with the Lean distribution's `leanchecker`, and all 22 named declarations used only subsets of `Classical.choice`, `Quot.sound`, and `propext`. The final declaration uses `Classical.choice`, `Quot.sound`, `propext`. [Composition driver](check.py)

| Record | SHA-256 |
| --- | --- |
| [Hosted report artifact](https://github.com/ProgramComputer/open-math-research/actions/runs/46004401561/artifacts/15201733806) | `e5ba9f2ba02a24e8d5ebbe4afc56993959e4f74751100075531fd285f98a3bec` |
| Extracted `angular-interlacing.log` | `582b937a8f1870d7ce20ceff39a93e0cb8f60eaa35c85f604ce4a1ab02e7ce19` |
| `RepositoryBoundedInterlacing.lean` | `879390e5d0649490035bc2bc4fc61a9764fdbd2a333ffb7a1d313cc37f4ea66f` |
