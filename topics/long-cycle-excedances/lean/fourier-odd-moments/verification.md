# Verification of the signed odd-pole moments

The [hosted source check](https://github.com/ProgramComputer/open-math-research/actions/runs/46019256689) passed for [commit 9dafab8](https://github.com/ProgramComputer/open-math-research/tree/9dafab8046662a698522b33b51ad052f2473d466). It used Lean 4.33.1 at compiler commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6 and mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. The checker authenticated the common dependency manifest and confirmed the checked-out package revisions.

All eight declarations report only propext, Classical.choice and Quot.sound. LeanChecker replayed both theorem modules with exit code zero. The shared pole definitions compiled at the same hash as the independent small-height contraction. [Hosted job](https://github.com/ProgramComputer/open-math-research/actions/runs/46019256689/job/140574306560) · [Reproduction command](README.md).

The checked result covers both complete signed sums when cutoff is at least 100, aspect is at least 44, and the stated size-sine lower bound holds. Both principal poles appear with weight one. The final theorem accepts the exact positive principal radius and uses the complex ratio in the row kernel. [Literal theorem](LiteralDiscretePoleMoments.lean).

[Report artifact 15207157568](https://github.com/ProgramComputer/open-math-research/actions/runs/46019256689/artifacts/15207157568) has ZIP SHA-256 367f704757bfa3e130fa5cebf9169cb63ebecacb5f7ffc54e0b4846c47bb250a and log SHA-256 ace31888ec6d848b245f7d0dc54c1b886feaba7ef9e50ed47e387d47897f7a63.

| Module | Compiled input SHA-256 |
| --- | --- |
| NumeratorLogDefinitions | 5b6c8d318b2d5f734c72a8b07087e929cc9e3edbac0109d82d9fdab7f8e765d1 |
| DiscretePoleEnvelope | d397d31a12c959d5da724b669a2d86e7937d871236db511b83a06dc316dc1c9f |
| LiteralDiscretePoleMoments | d5b7e5ef55a2a967b423907ffece907f04b5c9c49f072a12c20c6a4afa61f905 |
