# Comparing the minimum orbit length and the minimum load

Let $f$ be the probability that every orbit of a uniform permutation of $p$ colors receives at least $k$ of the $n$ independently assigned labels. Let $d(p,b)$ be the probability that all orbits of the color permutation have at least $b$ colors. The first event is Bowen Zuo’s unweighted slot probability. The estimates below compare the two events at the cutoffs used in the [exterior-root argument](../effective-front.md). [Zuo’s occupancy results](https://github.com/AlexZander-666/cycle-minimum-descent-real-roots/blob/e632c19bc246b819cd6b882cbf22c2fa9bc453de/formal/LongCycleBounds/OccupancyPositiveFloor.lean)

For positive $p,b$ with $n\ge200p$ and $4kp\le3nb$, one has

$$
f>d(p,b)-\frac{1}{250(2b-1)}.
$$

For $n\ge100p$, $a=kp/n\ge3/2$, and $b-1\le2a/3$, one has

$$
f\le d(p,b)+\frac{9}{1000a}.
$$

The first bound applies at $b=\lceil4a/3\rceil$ whenever that choice is at most $p$. If $b=p$ and $n\ge k$, a single orbit receives all labels, which gives $f\ge d(p,p)$ directly. The second bound applies at $b=\lceil2a/3\rceil$. [Quantitative statements](CutoffAcceptanceBudget.lean)

## Proof

Mark one orbit of $j$ colors that receives $i$ labels. Choosing the two supports, ordering the marked orbit cyclically, permuting its complement, and assigning the labels gives the mean number of such orbits as

$$
\frac1j\binom ni\left(\frac jp\right)^i\left(1-\frac jp\right)^{n-i}.
$$

If one event holds and the other fails, the word and permutation have an exceptional orbit. Selecting one such orbit embeds all those outcomes into the marked outcomes. With $X_j$ binomial with parameters $n$ and $j/p$, this gives

$$
d(p,b)-\sum_{j=b}^p\frac{\Pr(X_j<k)}j
\le f \le
d(p,b)+\sum_{j=1}^{\min(b-1,p)}\frac{\Pr(X_j\ge k)}j.
$$

This comparison includes fixed colors, unused colors, and empty words. It uses no independence between different orbit loads. [Counting and the injection](MarkedColorLoads.lean) · [First moments on the actual outcomes](MarkedLoadProbability.lean)

For the lower bound tilt the binomial generating polynomial by $3/4$. If $k\le3nj/(4p)$ the lower tail is at most $\exp(-nj/(32p))$. Putting $r=\exp(-n/(32p))$, summing over $j\ge b$ costs at most $r/[b(1-r)]$. Since $n/p\ge200$, we have $r<1/501$, which gives the stated bound.

For the upper bound tilt by $3/2$. When $nj/p\le2k/3$, the upper tail is at most $\exp(-k/15)$. There are at most $b-1$ relevant lengths. Put $\mu=n/p$. Since $\exp(a\mu/15)\ge(a\mu/15)^3/6$, $a\ge3/2$ and $\mu\ge100$ give $(2/3)a^2\exp(-k/15)\le9/1000$. [Binomial tails](BinomialColorLoad.lean) · [Sums over orbit sizes](ColorLoadRanges.lean) · [Scalar bounds](LoadEnvelope.lean)

## Bounds for the original coefficients

Let $\alpha_p=[t^p]E_{n,k}(t)/p^n$ and $a=kp/n$. For $1\le b\le p$, counting permutations by the cycle containing a distinguished color gives $1/(2b-1)\le d(p,b)\le1/b$. The first block $b\le p<2b$ has $d(p,b)=1/p$. Beyond it, the recurrence $p d(p,b)=(p-1)d(p-1,b)+d(p-b,b)$ propagates both bounds. The color permutation's orbit lengths agree with its minimal positive return times, including fixed points. [Orbit lengths and normalized permutation counts](RepositoryOrbitBaseline.lean)

When $n\ge10000$, $k\ge2$, $4000k<n$, $p\ge1$ and $4p^2\le n$, the checked Lean theorem gives

$$
\frac{99}{100(1+8a/3)}\le\alpha_p\le\min\left(1,\frac{151}{100a}\right).
$$

For the lower estimate take $b=\lceil4a/3\rceil$. The surplus from the formal series transform costs at most $3/4000$ after multiplication by $2b-1$. For the upper estimate take $b=\lceil2a/3\rceil$ when $a\ge3/2$, and use the probability bound of one for smaller $a$. The coefficient at $p=1$ is exactly one. [Original coefficient bounds and precise hypotheses](RepositoryColorAlpha.lean)

## The insertion lag

Let $V$ denote the full lag polynomial in the insertion recurrence and $L_p=[t^p]V/p^n$. The successor identity and the upper bound one on the residual acceptance probability give

$$
L_p\le\sum_{j=0}^{p}\binom n{k-1}(j/p)^{k-1}(1-j/p)^{n-k+1}.
$$

For $d=k-1>0$ with $2d\le n$, the sum is at most $p/(n+1)+1/\sqrt d$. The finite mesh estimate for a unimodal density costs one maximum in addition to $p$ times its integral. A primitive obtained by telescoping Bernstein polynomials gives the integral $1/(n+1)$. The proof uses Bowen Zuo’s binomial atom estimate from the authenticated cutoff-six archive to bound the maximum. [Finite mesh](FiniteUnimodalMesh.lean) · [Bernstein primitive](BernsteinProbability.lean) · [Grid for the actual load](RepositoryBinomialGrid.lean) · [Zuo’s supplying estimate](https://github.com/AlexZander-666/long-cycle-excedance-interlacing/blob/46dc6e9cc3d768ae8b1ed41617d4b1eef9b1b554/LongCycleBounds/BandBinomial.lean#L77-L86)

For $k\ge150$ this grid estimate and the lower bound for $\alpha_p$ give $L_p<\alpha_p/8$. For $8\le k<150$ the small-rank hypotheses force $a\le3/4$. The lower binomial tail then bounds the grid by a geometric series of sum at most $1/500$, which suffices for the same conclusion. At every rank $j\ge0$ the lag also satisfies $0\le[t^j]V\le j^{n+1}$ by comparison with the transformed successor row. The checked Lean theorem supplies the near-lag hypothesis of the exterior reduction for every $0\le j\le\lfloor\sqrt n/2\rfloor$, including the zero coefficient at the origin. [Small-cutoff grid](SmallLagGrid.lean) · [Relative lag](RepositoryUniformLag.lean) · [Near and global bounds on the original rows](RepositoryExteriorLag.lean)

## Verification

The hosted Lean 4.33.1 build at commit `fe49dc0d879b6ff53fe3fbc343bd598d85b01a25`, mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, compiled and replayed all 22 load modules and three original probability modules. All 25 source hashes matched their Git blobs. All 65 declarations printed by these modules and all 285 registered declarations in the composed run used only standard axioms. Earlier failed runs identified porting errors in filter instances, derivative rewrites, order lemma orientation and implicit theorem arguments. The final build passed. [Verification record](verification.txt) · [Hosted run](https://github.com/ProgramComputer/open-math-research/actions/runs/45962395508/job/140383048823)

A literal enumeration independently checked 280 marked-load probabilities on 137,883 word–permutation pairs and both comparisons in 588 quadruples. The checker includes $0\le n\le6$, $1\le p\le4$, $1\le k\le6$ and $1\le b\le p+1$. [Exact checker](check-marks.py) · [Output](marked-output.txt) · [Research pull request](https://github.com/ProgramComputer/open-math-research/pull/280)

~~~sh
python3 -I topics/long-cycle-excedances/color-load-bounds/check-marks.py
python3 -I topics/long-cycle-excedances/lean/common-pin/check.py /tmp/orbit-load-research
~~~

An independent exact calculation checked 44 positive ranks across four large rows. The case $(n,k)=(10^6,8)$ lies in the logarithmic interlacing sector. The other cases exercise the coefficient estimates, including cutoffs 150 and 300. Each calculation recovers the lag in two ways, and the generating series agreed with literal enumeration on 39 complete small rows. [Generating series and input ranges](coefficient-check.md) · [Exact output](coefficient-output.txt)

The large-size interlacing theorem also needs the two weighted old-row tails, the weighted far-lag bound, and positivity, order and size control for consecutive coefficient-ratio centers. [Remaining hypotheses on the original rows](../lean/front-envelope-sums/RepositoryExteriorEnvelopes.lean) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)
