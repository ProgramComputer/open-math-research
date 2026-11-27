# Independent agent-assisted review

Verdict. The proposed argument proves the stated partial theorem for every integer threshold $`j\ge2`$ and every integer $`3j\le n<5j`$. Both consecutive rows have simple negative roots. Their strict order is the direction specified in the ordered-partition conjecture. The earlier reviewed result covers the transition into degree three, and the new cubic range includes the transition into degree four. The new quartic range reaches the transition into degree five. The original conjecture also asks about subsequent pairs, which these certificates leave open. I reviewed the mathematical argument and its computation. No Lean or Rocq verification was part of this review.

The [primary source](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) sums over sequences of nonempty labeled blocks and marks each block of size at least $`j`$. The previously published [PR #242](https://github.com/ProgramComputer/open-math-research/pull/242) joins through the first cubic row. For $`j\ge2`$, selecting $`k`$ blocks of size exactly $`j`$ and filling with singletons gives nonzero coefficient support for every $`0\le k\le\lfloor n/j\rfloor`$. The same-degree ordering starts with an old root when ordered on the real axis from left to right, since the new root nearest zero has the smallest modulus. A carry gives the new row one extra root at the far left. Both agree with the [catalog's interleaving definition](https://www.symmetricfunctions.com/realRootedInterlacing.htm).

I checked the expansion about the mark one, the common affine coordinate, and the Laurent and forward-difference intervals. The Cauchy inequality follows on the radius-four circle and the negative-index binomial tails grow more slowly than the geometric envelope. Convolution needs the uniform negative-index error, since the excess can exceed the requested coefficient index. The estimate for the $`k=0`$ difference is valid with its clipped exponent because $`j2^{-dj}`$ is decreasing. The extra top term occurs exactly when $`n+1=(d+1)j`$, and the rectangle test includes that locus. The final seam's slope lower bound is preserved by convolution with any nonnegative sequence, because each contributing index is at most the target index. At the largest old root, the reversed equation and the seam inequality force the desired sign even when the leading coefficient approaches zero. Away from that seam the rational endpoint signs and strict difference signs suffice. At the carry the leading term of the new row creates the extra root after the greatest old root in the normalized coordinate. The degree count makes all displayed roots simple.

The negative Bézout form proof has the correct sign. At an old root its value is $`-P'Q`$ up to a strictly positive factor. Independently, I implemented a primitive-integer signed remainder check and reconstructed both coefficient tables by a column-wise first-block recurrence. The ordinary Sturm index of $`P'/P`$ was $`d`$ in every pair. The signed index of $`-Q/P`$ was also $`d`$, so each simple real pole contributes positively. This gives the strict inequality $`-P'(r)Q(r)>0`$ at every old zero. Both methods yield the same coefficient-ledger hashes.

| Old degree | Uniform cutoff | Rational rectangles | Ordinary brackets | Seam brackets | Residual equal degree | Residual carries |
|---|---:|---:|---:|---:|---:|---:|
| 3 | 64 | 73 | 216 | 3 | 1,953 | 62 |
| 4 | 128 | 1,615 | 6,451 | 9 | 8,001 | 126 |

Cubic coefficient ledger SHA-256 is `e3c72df0a2e676889ab51a1c48f773358cb3cf512f179366841f2637c86addb6`. Quartic coefficient ledger SHA-256 is `6ecd607b899c6d9e7486b1699e27f67487e3bd6e36e3ae06472b242bbaa22313`.

~~~sh
python3 replay.py finite-3-64.json finite-4-128.json
python3 independent-finite.py 3 64
python3 independent-finite.py 4 128
~~~

The displayed commands leave Python assertions enabled.

| Reviewed file | SHA-256 |
|---|---|
| proof.md | `37f9e9e0657c3673a03bd11b85a941ef5f47cee198861d07f802e71e5f659e77` |
| finitej.py | `430088d6fd72b0f73167fb4b10f5ffd7c09ab2082290dfad4f840dbe16637a02` |
| replay.py | `12f164b6c79d0a3fce58c7d00b706f9def152e4666dc50d300dffdcebb52753b` |
| finite-3-64.json | `47d3c6d91a5b537e90490be5457d894bd16cb56c840a1b7b8990d6bbc8da1153` |
| finite-4-128.json | `ad3421a5032816b2ffb8e69486e7d02d6ba2aca704f369ac23961ae9b4572cec` |
| all-finite.py | `cc4c33a4bde8f857979aec4a8d6a9b9726ea80ffa8251eaba2c15acd7103002a` |
| independent-finite.py | `583361cda84f058f1c4d4f5b16a269931d6843d7d1bd3b310a8a0c7667e2ea8d` |

The hashes above identify the inputs supplied to the independent reviewer. The repository edition reformats the Python, rejects execution with assertions disabled, and explicitly checks that the verified coefficient error multiplier is one. It also records the final quartic count and copyedits the mathematical notation. The JSON certificates and mathematical tests are the reviewed ones.
