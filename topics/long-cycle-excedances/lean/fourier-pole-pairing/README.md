# Finite conjugate pairing of the enclosed Fourier poles

Let $P_l=s+(2l+1)i\pi$. Assume $|P_0|<R$ and let $P$ be the finite set of all $P_l$ with $|P_l|<R$. Define the positive count and the positive nonprincipal index set by

$$
 N=\left\lceil\frac{\sqrt{R^2-s^2}/\pi-1}{2}\right\rceil,\qquad
 I=\{0,\ldots,N-2\}.
$$

The principal enclosure gives $N\ge1$. The set $I$ is empty when $N=1$. For every natural index $j$, the exact positive enclosure test is $j<N$. Thus the upper half of $P$ consists of the principal pole $P_0$ and $P_{i+1}$ for $i\in I$. The lower half uses the reflected indices $-j-1$. If the radius is regular, the same $I$ is obtained from the existing weak enclosure predicate. [Stock positive-enclosed-poles membership](../middle-residues/RepositoryEnclosedHalf.lean).

For any term $b$ with $b(\overline p)=\overline{b(p)}$ on $P$,

$$
 \frac{\mathrm{Re}\sum_{p\in P} b(p)}{2}
 =\mathrm{Re}\,b(P_0)+
   \mathrm{Re}\sum_{i\in I}b(P_{i+1}).
$$

The same $I$ serves the old and adjacent terms. The proof uses the literal pole definition, its injective index map, conjugation, and the exact norm square. It sums the two disjoint images of the positive index range and separates its index zero. [Finite pairing and index theorems](EnclosedPolePairing.lean).

Run the [common-pin check](check.py) from the repository root with Lean 4.33.1 first on the path.

    python3 -Bu topics/long-cycle-excedances/lean/fourier-pole-pairing/check.py /tmp/fourier-pole-pairing

The [hosted workflow](../../../../.github/workflows/long-cycle-enclosed-pole-pairing.yml) uses the original Fourier pole and signed-moment inputs, strict compilation and the bundled LeanChecker replay.
