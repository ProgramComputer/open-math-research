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

## Verification

The six modules were developed and compiled on Lean 4.19. The 16 named declarations had only the standard axioms in that development build. The common research pin is Lean 4.33.1. Its port and kernel replay are pending. A literal enumeration independently checked 280 marked-load probabilities on 137,883 word–permutation pairs and both comparisons in 588 quadruples. The checker includes $0\le n\le6$, $1\le p\le4$, $1\le k\le6$ and $1\le b\le p+1$. [Exact checker](check-marks.py) · [Output](marked-output.txt)

~~~sh
python3 -I topics/long-cycle-excedances/color-load-bounds/check-marks.py
python3 -I topics/long-cycle-excedances/lean/common-pin/check.py /tmp/orbit-load-research
~~~

The remaining original-row estimate requires bounds on $d(p,b)$ and the local mass of the insertion lag, together with the conversion from the color probability to the permutation coefficient. These bounds address the high-rank part of the uniform exterior proof for cutoffs eight and above. [Exterior coefficient criteria](../lean/front-middle-join/README.md) · [Tracking issue](https://github.com/ProgramComputer/open-math-research/issues/4)
