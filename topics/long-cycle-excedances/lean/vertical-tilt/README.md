# Phase and amplitude of the enclosed odd poles

Let $k\ge7$, $x\ge10\sqrt{k}$, $w_p=x+ip\pi$ for odd $p$, $r=|w_1|$, $S=\pi/r$ and $R=r(1+1/(50k))$. Write $T=\exp G$ for the tilt in the generating function of permutations with minimum cycle length $k$, counted by excedances. For enclosed odd poles $p<q$ with $|w_p|,|w_q|\le R$,

$$
|G(w_q)-G(w_p)|<\frac{12}{25}(q-p).
$$

The conjugate pair $p=-1$ and $q=1$ gives $|\Im G(w_1)|<12/25$. For every $x\ge0$, if $nS^2\ge1$ and $F$ is any finite set of positive odd integers $p\ge3$ with $|w_p|\le R$, then

$$
\sum_{p\in F}p\left(\frac{r}{|w_p|}\right)^n\left|\frac{T(w_p)}{T(w_1)}\right|\le\frac15.
$$

These inequalities bound the contribution of the positive nonprincipal poles to the normalized consecutive-row estimate. The [uniform all-cutoff argument](../../effective-uniform.md) used $21/50$ for the same sum. The passage from the residues to signs at every root also requires control of the row remainder and the exterior roots. [Actual phase and tilt](RepositoryPoleTransport.lean) · [Actual weighted sum](RepositoryMinorPoles.lean) · [All-angle result](AllAngleMinorPoles.lean) · [All-angle result](AllAngleMinorPoles.lean) · [All-angle result](AllAngleMinorPoles.lean)

## Proof

Set $t=-e^{-x}$ and write $G(w)=\sum_{d=1}^{k-1}g_dw^d$. The Eulerian moment formula gives $-d!g_d=\sum_{a\ge1}t^aa^{d-1}$, including the geometric series at $d=1$. Since $e^{-w_p}=t$ at every odd pole, the difference of $G$ at two poles is the negative sum of the differences of the functions

$$
H_a(w)=\frac{e^{-aw}}a\sum_{d=0}^{k-1}\frac{(aw)^d}{d!}.
$$

The constant terms cancel and the degree sum is finite. [Discrete moments](RepositoryLogTiltDiscrete.lean) · [Exact difference](PoleModeIdentity.lean)

Put $m=k-1$ and $f_m(y)=e^{-y}y^m/m!$. On the vertical chord the radius bound gives $|w|^m\le x^m e^{7/100}$. Differentiating each finite exponential gives $|H'_a(w)|\le e^{7/100} f_m(ax)$. The sum of these derivative bounds is finite. The proof bounds the change of each summand before summing. [Radius](VerticalRadius.lean) · [Termwise transport](VerticalTransport.lean) · [Summation](VerticalMeshSum.lean)

For $k\ge14$, the samples of the nonnegative unimodal density satisfy $\sum_{a\ge1}f_m(ax)\le 1/x+f_m(m)$. To see the mesh bound, remove the increasing function $y\mapsto f_m(\min(y,m))$. The remainder is decreasing, so each right-endpoint sum exceeds its integral by at most one telescoping increment of the removed function per interval, after division by the mesh spacing. The total excess is at most the height of the mode. The sequence $f_m(m)$ decreases, and $f_{13}(13)\le1/9$ follows from $e>2.718$. Since $x\ge37$, this gives $\pi e^{7/100}\sum_{a\ge1}f_m(ax)<12/25$. For $7\le k\le13$, one has $x\ge24$ and $x\ge2m$. A truncated exponential bound gives $f_m(ax)\le10^{-a}$ and the same strict estimate. Integrating along the straight chord between the two poles gives the first inequality. [Unimodal mesh](UnimodalMesh.lean) · [Gamma density](GammaDensity.lean) · [Peak bound](GammaPeak.lean) · [All cutoffs](AllCutoffMesh.lean)

For an enclosed pole put $z=(p^2-1)S^2$. The identity $|w_p|^2/r^2=1+z$ and enclosure imply $0\le z\le1/49$. From $\log(1+z)\ge z/(1+z)$ and $nS^2\ge1$ we obtain $(r/|w_p|)^n\le e^{-49(p^2-1)/100}$. The chord gives $|T(w_p)/T(w_1)|\le e^{12(p-1)/25}$. For $p=2j+1$, $j\ge1$, the combined exponent is at most $-74j/25$. Now $e^{74/25}>18$ and $2j+1\le3^j$, so each weighted term is at most $6^{-j}$. Their sum is at most $1/5$. [Radial estimate](MinorPoleRadius.lean) · [Geometric series](MinorPoleMass.lean)

For $0\le x\le10\sqrt{k}$, the enlarged disk contains no nonprincipal poles. Indeed, $r^2=x^2+\pi^2\le102k$ and $R^2-r^2\le(3/(50k))r^2\le306/50$, whereas the first nonprincipal pole lies at squared distance $r^2+8\pi^2$ from the origin. This proves the sum bound throughout the middle range. The squared radius ratios summed over the entire signed pole lattice are also bounded by $2+n/2$. [Exclusion estimate](SmallRadius.lean) · [Both all-angle statements](AllAngleMinorPoles.lean)

## Verification

Independent agent reviewers checked the discrete moments, pole orientation, density and radius estimates, the positive-side summation, and the full range in $x$. [Independent review](independent-review.md)

The shared research-pin rebuild and replay are pending. The [all-cutoff interlacing result](../../all-cutoffs/README.md) has 🟨 Partial · Lean 4 coverage.
