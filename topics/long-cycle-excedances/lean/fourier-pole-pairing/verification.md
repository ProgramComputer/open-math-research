# Verification of the enclosed pole pairing

The [hosted common-pin check](https://github.com/ProgramComputer/open-math-research/actions/runs/46023492844) passed at [commit 30989b0](https://github.com/ProgramComputer/open-math-research/tree/30989b03a9598e59dab13222acc38afce10114e3). It used Lean 4.33.1 at compiler commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6 and mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. The checker reused the authenticated common-pin archive and checked the pinned package revisions.

All five named declarations report only propext, Classical.choice and Quot.sound. The finite pairing module replayed through LeanChecker with exit code zero. The exact compiled source and four dependency hashes match the repository. [Hosted job](https://github.com/ProgramComputer/open-math-research/actions/runs/46023492844/job/140588820919) · [Reproduction command](README.md).

The [literal source](EnclosedPolePairing.lean) proves the natural-ceiling count, the positive finite image, compatibility with the weak-enclosure index set at a regular radius, and the complex and real finite pairing formulas for a conjugate-equivariant term. The signed contour identity and magnitude estimates use this same set in their respective components.

[Report artifact 15210422856](https://github.com/ProgramComputer/open-math-research/actions/runs/46023492844/artifacts/15210422856) has ZIP SHA-256 b9900abc24917f8ed9b5850f8f8cda6c3b0f67925d16bf9a89488e74e2ba28c8 and log SHA-256 d87fbeada90020e091215e6793145e483a52b2d7f3e5020f5fde8dee42d4fcef.

| Module | Compiled input SHA-256 |
| --- | --- |
| NumeratorLogDefinitions | 5b6c8d318b2d5f734c72a8b07087e929cc9e3edbac0109d82d9fdab7f8e765d1 |
| DiscretePoleEnvelope | d397d31a12c959d5da724b669a2d86e7937d871236db511b83a06dc316dc1c9f |
| LiteralDiscretePoleMoments | d5b7e5ef55a2a967b423907ffece907f04b5c9c49f072a12c20c6a4afa61f905 |
| FourierAnchoredLogistic | 4fb5fa1ae84762bd6d02731bb14445357d458abb9809bead666485d68d819c11 |
| EnclosedPolePairing | 031d5af688e405ad9890a2f56a46e9dd13e71f84cd1e26bfcdcd8f62bcc1e9bc |
