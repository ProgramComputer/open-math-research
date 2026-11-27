# Independent relative-margin replay

I evaluated all 2,164,796 sign claims in the authenticated 22-shard witness archive with the unrounded GMP insertion row and a new relative test. The checks cover 82,395 consecutive pairs and 541,199 brackets. The stream has 63,014,205 bytes and SHA-256 8f8115d4f203840560dd74f7cf12654d0bca00561c8ff473f27ed6af3f20a73e. The new test passed for every claimed sign in 65.94 seconds on this host, using 29 exact rational tail comparisons. The checker does not use a homogeneous prefix fallback.

I took $H$ to be the alternating floor-Horner prefix and $A$ the positive ceil-Horner prefix on the first 60 exact coefficients. Each floor error contracts by $0<y<1/2$, so all floor errors affect the final value by less than two. Write $T$ for the geometric bound on the omitted tail. Then $\sigma P(-y)\ge\sigma H-2-T$ and $P(y)\le A+T$. I checked $2^{32}(\sigma H-2)-A>(2^{32}+1)T$. Where the coarse bound on the tail ratio was insufficient, I used the exact positive denominator of the geometric tail.

At cutoff 13 and new size 256, I used the left endpoint of the rank-32 bracket of the pair with old size 255. The required sign is positive. The endpoint has numerator 871689497096755307205496065384395168305363817049 and denominator $D=2^{170}$. My separate Python program used the explicit Eulerian formula and distributed the insertion terms into the complete row. With $F=D^{254}P(-y)$ and $G=D^{254}P(y)$, all 255 coefficients give $2^{31}F<G<2^{32}F$. The ratio is approximately $3.83980901467295134536\times 10^{-10}$.

The result concerns the numerical conditioning of this finite certificate. The comparison is on the literal reduced row; it depends on the same verified coefficient interpretation and tail bound as the previous strict sign checker. The replay is independent executable arithmetic and is outside Lean.

Agent-assisted independent arithmetic review, 26 November 2026 (America/Chicago). The archived verification scripts reproduce the reference full-degree comparison.

## Directed arithmetic review

A second agent reviewed the directed checker at commit `86307df`. Converting a positive GMP integer keeps its leading 60 bits and rounds upward exactly when discarded bits are nonzero. Normalization handles a carry into the next exponent. Sums of aligned significands fit in 61 bits and products in 120. The input bounds on row size, endpoint exponent and line length keep the intermediate exponents within the supported signed integer range.

Both clamped differences subtract nonnegative quantities. If the first difference returns zero, the second cannot become positive. The checker accepts only a strictly positive final difference $m$, for which both subtractions genuinely provide lower bounds. Its directed comparison then proves $m(u-yv)>(1+2^{-32})u^2y^{60}$. In particular the geometric-tail denominator is positive. The reviewer accepted the check under the documented coefficient enclosure, tail majorant and authentication of the archive. The directed implementation was reviewed as C++.
