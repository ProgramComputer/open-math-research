# High-height numerator contraction

Let $k\ge100$, $s>4\sqrt{k}$, $w_1=s+i\pi$ and $r=|w_1|$. Put $t_r=(1-1/k)r$. For $r\le |w|\le (1+1/k)r$, set $\widehat w=t_r w/|w|$ and $\widehat w_1=(1-1/k)w_1$. The [common-circle argument](../../fourier-circle/README.md) uses the estimate

$$
|G(w)-L(\widehat w)|+|G(w_1)-L(\widehat w_1)|<25 .
$$

Here $G$ is the cutoff logarithm for the original strict-excedance numerator, and $L(z)=\log((1+\exp(z-s))/(1+\exp(-s)))$ at the contracted arguments. This improves the constant 30 for the high-height arm of the common-circle bound. The small-height arm includes the split equality.

## Literal coefficients and log branch

At $t=-\exp(-s)$, the existing repository theorem `RepositoryQuotientAudit.seriesValue_original_coherentTilt` identifies the actual numerator with the exponential of the finite polynomial

$$
G(w)=\sum_{d=1}^{k-1}\mathrm{cutoffLogCoefficient}(k,t,d)w^d .
$$

The coefficient at $d=1$ is $-t/(1-t)$. For $2\le d<k$, the coefficient is $-t A_{d-1}(t)/(d!(1-t)^d)$ by deleting cycles of length $d$ in the exponential formula. The existing `RepositoryQuotientAudit.cutoffLogCoefficient_hasSum` verifies the shifted discrete Eulerian moment

$$
\sum_{a\ge1}t^a a^{d-1}=-d![w^d]G(w).
$$

Consequently, with $E_{<k}(x)=\sum_{d=1}^{k-1}x^d/d!$, the value $G(w)$ has frequency expansion $\sum_{a\ge1}(-t^a/a)E_{<k}(aw)$. There is no constant term to retain. The $d=1$ expansion uses the geometric series and the higher degrees use the Eulerian power sums, so both follow the same sign and the same frequency origin.

On $|z|<s$ the two arguments $-\exp(z-s)$ and $-\exp(-s)$ have modulus below one. The ordinary complex log Taylor theorem on that disk gives

$$
L(z)=\sum_{a\ge1}\frac{-t^a}{a}\bigl(\exp(az)-1\bigr).
$$

The logarithm difference equals the principal logarithm of the quotient because the denominator $1+\exp(-s)$ is positive real. The contracted radius is below $s$, as shown below. These facts fix the same analytic logarithm normalized by $L(0)=0$.

## Scalar bounds

The relation $r^2=s^2+\pi^2$ gives $r\ge s$ and $(r-s)2s\le\pi^2<9.92$, so $r-s<.31s/k$. At $k\ge100$ it also gives $r<1.004s$, $(1+1/k)r-s<1.314s/k$ and $s-t_r>.69s/k$, with $t_r>1$.

For a radius $R$ and frequency $a\ge1$, write

$$
F_a(k,s,R)=\exp(-as)\sum_{j=0}^{k-2}\frac{(aR)^j}{j!}.
$$

The radial change from $R$ to $t_r$ costs at most $(R-t_r)\sum_a F_a(k,s,R)$. This follows termwise from the real power-difference inequality for points on the same complex ray. The degree factor cancels the factorial and the frequency factor cancels $1/a$. At $R=r$ the same formula uses width $r/k$.

Suppose $s\le R$ and $R-s\le D s/k$ with $1/50>D/k$. Below $a=5k/(4s)$ the summands are at most $\exp(5D/4)$ and the number of positive frequencies is at most $5k/(4s)$. Above this split $aR>5k/4$. The lower-degree exponential sum is at most $\exp(49aR/50)$. Indeed tilting the positive terms by $4/5$ costs at most $(5/4)^k\le\exp(9k/40)$, which follows from the quadratic Taylor lower bound at $9/40$. The upper-frequency contribution is therefore at most $1/((1/50-D/k)s)$ by the geometric bound $\sum_{a\ge1}\exp(-ac)\le 1/c$.

At radius $t_r$, the remaining Taylor tail is bounded by

$$
\sum_{a\ge1}\frac{\exp(-as)}a\sum_{j\ge k}\frac{(at_r)^j}{j!}.
$$

If $at_r\le k/2$, tilt the positive terms by $2$ and use $\log 2\ge2/3$. A single weighted contribution is bounded by $\exp(-k/6)$ since $1/a\le1$ and $t_r<s$. There are fewer than $k$ such frequencies since $t_r>1$. The eighth positive Taylor term of $\exp(k/6)$ gives $k\exp(-k/6)\le1/1000$ for all $k\ge100$. Above the split use $1/a\le2t_r/k$ and the full exponential series. The geometric contribution is at most $2t_r/[k(s-t_r)]\le2/.69$. Both contractions have the same tail bound.

After multiplying the two radial contributions by their respective widths, the total is at most

$$
2(1.004)(5/4)e^{657/400}+(1.004)(5/4)e^{31/80}
+\frac{2(1.004)}{k/50-1.314}+\frac{1.004}{k/50-.31}
+2\left(\frac1{1000}+\frac2{.69}\right)<25 .
$$

The last comparison uses rational Taylor upper bounds on the two fixed exponentials and monotonicity of the denominators from $k=100$. The wider-circle proof's tighter-looking $r/s<1.001$ is only used there with $k\ge400$. The present proof uses $1.004$ at the smaller cutoff.

## Verification and scope

Local Lean 4.19.0 with Mathlib at `c44e0c8` checks the two exponential tilts, finite geometric domination, geometry, exact numerical budget, infinite summability for both frequency majorants, the complex logarithm expansion, the cutoff-moment adapter with a supplied moment, and the resulting contraction. These declarations use only propext, Classical.choice and Quot.sound. Lean 4.33.1 checks the original permutation wrapper through the authenticated `RepositoryLogTiltDiscrete` moment. The local wrapper imports the exact-definition interface with the supplying Eulerian moment expressed as a parameter. The denominator and final angle-sign argument have separate verification.

The [research checker](check.py) builds the original wrapper at the pinned Linux compiler and prints the SHA-256 of each source, each required axiom report and each bundled LeanChecker exit. Run from the repository root with Lean 4.33.1 on PATH.

```sh
python3 -Bu topics/long-cycle-excedances/lean/fourier-high-height/check.py /tmp/high-height-replay
```

Use `--retained-imports /path/to/quotient-import-objects.tar.zst` to reuse the authenticated common-pin build objects. Without that option, the checker builds the supplying source closure.

[Independent mathematical review](independent-review.md) · [Literal cutoff coefficient moments](../vertical-tilt/RepositoryLogTiltDiscrete.lean) · [Logarithm branch](HighHeightPointAdapter.lean) · [Original cutoff numerator statement](RepositoryHighHeightNumerator.lean)


## Production replay

The [hosted build](https://github.com/ProgramComputer/open-math-research/actions/runs/46014956766) checked the exact proof source `8128b9d4513375141bf80ec34aa0a1b7eb15c9d6` with Lean 4.33.1 at `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and frozen upstream source `46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554`. The 17 local source hashes match the Git blobs and the 11 frozen hashes match the supplying source archive. Lean’s bundled LeanChecker replayed 15 modules. The dedicated audit passed all 26 named declarations. The exact original theorem `RepositoryQuotientAudit.original_high_height_numerator_contraction` lists propext, Classical.choice and Quot.sound.

The verification [archive](https://github.com/ProgramComputer/open-math-research/actions/runs/46014956766/artifacts/15205967208) has SHA-256 `fb07d2f7be7f8f3930cf9f88711892218e3848934a9a961897b674f14ac52576`. The extracted console has SHA-256 `e3451d128abdbb7c4e8f3a2a39b22c841b85273c9693d795adf60f45cc81c5d7`. The continuation option added to the shared Fourier driver is inactive for this replay. Source inspection and a traced comparison confirm that the original-log invocation performs the same preparation and build calls.
