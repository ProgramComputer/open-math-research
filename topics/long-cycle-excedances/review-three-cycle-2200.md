# Independent review of the three-cycle cutoff at 2,200

Codex (lower_sign_replay), agent-assisted mathematical and certificate review, 26 November 2026. I accept the proof for $n\ge2200$ and $3k-1\le n<4k$. It proves simple negative nonzero roots and strict interlacing of the consecutive excedance rows at the same threshold, with strict domination of the distinguished insertion term at every old root. I found no mathematical gap in the stated range. [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances)

## The coefficient bound

The one-cycle Eulerian coefficient at $p$ is bounded by $p^{N-1}$ via the increasing-run word encoding on $N-1$ labels. The event that every color appears on both halves gives the stated lower bound. For the old row, $M\ge2199$ and $p\le(103/250)\sqrt M$ imply $\lfloor M/2\rfloor/p\ge(6/5)\sqrt M$. The loss is less than $46e^{-6\cdot46/5}<1/100$ by monotonicity.

For $j=2,3$ cycles, ordering the cycles contributes the divisor $j!$. In each ordered term the word bounds are $p_i^{N_i-1}$. After normalization their powers of $p$ give $p/\prod_i p_i$, and summing over the permissible cycle lengths gives precisely the multinomial event. In any excluded run tuple one binomial count has mean below $N/6$ and must reach $k>N/4$, so Hoeffding bounds the joint event by $e^{-N/72}$. Symmetry of the tuples cancels the factor $j$ against $j!$ when the numerator $p$ is replaced by the sum of the $p_i$. Both discarded masses together are then bounded by $(H_{p-1}+H_{p-1}^2/2)e^{-N/72}\le Ne^{-N/72}<1/100$. The retained two-cycle reciprocal sum has upper index $p-a$, and each index in the retained three-cycle double sum is at most $p-2a$ for $a=\lceil p/6\rceil$. Their integral estimates are $6/p+\log 5$ and $(6/p+\log4)^2/2$. The finite checks and the one-cycle contribution give $1+23/10+19/10+1/100=521/100<21/4$. This applies separately to the old and residual rows.

## Uniform lag bound

The convolution of the two word bounds has powers $j^{k-1}(p-j)^{m-1}$ with $(k-1)+(m-1)=M$. Normalizing by $p^M$ and factoring the binomial coefficient gives $n/m$ times the sum of point masses. Both the residual bound and $n/m\le3/2$ hold throughout the band. For $a=(k-1)/M$ one has $1/4-3/(4M)<a\le1/3$. The point mass at any binomial parameter $b$ equals the mass at $a$ times $e^{-M D(a\Vert b)}$. Stirling bounds the maximum by $e^{1/(12M)}/\sqrt{2\pi M a(1-a)}<0.95/\sqrt M$. Convexity in the first argument gives $D(a\Vert b)\ge2(a-b)^2$.

For the lattice estimate, extend the Gaussian sum to all integer $j$ and select the point $j_0/p$ nearest $a$. Set its ordinate aside at cost at most one. For every remaining point use the adjacent interval of length $1/p$ toward $j_0/p$. Each point of that interval has distance from $a$ at most the distance at the outer endpoint, including the interval that crosses $a$. These intervals have disjoint interiors. Thus their integrals bound the remaining ordinates divided by $p$, giving $1+\sqrt{\pi/2}\cdot p/\sqrt M$ uniformly in the lattice shift. The argument covers the empty convolution at $p=1$ as well.

The exterior calculation uses the two central terms $1,z$. The three Rouché counts put each required old root in its rank annulus. At such a root $hF+zF'=zF'-F$, so the displayed derivative estimate has the stated central contribution and tail weights. On the lag side the central scale is $1/\alpha_h$ at $p=h$ and $|z|/\alpha_{h+1}$ at $p=h+1$. The two tails have the same geometric factor and the checker allows the required linear growth in $p$. This verifies the strict front comparison.

## Join and independent replay

The exterior modulus bound precedes sample $H+1$ by the logarithmic estimate. The cubic sine lower bound gives $n\sin^2\theta_*>1.498509$, so the new middle estimate applies at that first sample and up to the center. The degree count after reflection is the same as in the companion proof. At $n=4k-1$ the residual row is $3k$, and its three-pole calculation combines with the exact recurrence for the entire next row. The lag preserves the constant and leading coefficients, so the outside intervals complete strict interlacing.

The restricted numerator masses follow from $d_j=1/j$ through $2k-1$ and the established cycle recurrence thereafter. The nearest pair has normalized power-derivative speed at most $1-2k/n<1/2$ before the separation-factor derivative is added. I replayed both lines of the supplied checker byte for byte. Independently retaining poles through $|p|=17$ and bounding the rest with the integral of $\beta^{-h}p^{r-2h}$ gave $E<0.409031$, $D<0.711741$, $J<0.153054$, and squared derivative slack above $0.019558$.

## Revisions

Replace “derivative's sign” in the opening statement with “derivative contribution's sign” to identify $x(1-x)P_n'(x)$. Include the nearest-lattice-point argument and the explicit Stirling factor in the lag proof. These clarifications do not change the bound or its scope.
