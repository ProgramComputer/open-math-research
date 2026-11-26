# Independent review of the effective upper angular estimate

**Verdict.** The stated constants give a strict sign for the sum of the leading Gaussian terms at $k=D-1$ and $k=D-2$, for every $d\ge10^{12}$, $n\ge64d$, and $1\le r<d$. The estimate controls only those terms. Transverse approximation and localization would need separate bounds to transfer the sign to the actual balanced-array polynomial.

## Uniform constants and angular branches

At $x\le1/16$, the successive deficit weight ratios bound the unweighted relative weights by $x^j$. The ratio of the covariance weight at $j$ to its value at zero is at most $j+1$, even at $j=r$ where it vanishes. This gives $p_0\ge1-x$, $p_1=xp_0$, and $\tilde p_0\ge(1-x)^2$. The three raw moment bounds follow by differentiating the geometric series. At $x=1/16$, the upper bounds after factoring out $x$ are $8192/3375$, $16384/5625$ and $1015808/253125$, strictly below $3,4,5$, respectively. Centering costs at most $(3x)^3$, and $5x+(3x)^3\le6x$.

For every real $t$, both characteristic functions lie within distance $31/128$ of one by their masses at zero. Consequently $|G/F-1|\le62/97<1$. This proves positive real part of the transverse variance and identifies its Gaussian branch for every angular label. At $|t|\le1$ the centered characteristic functions have real part at least $7/8$ and imaginary part at most $x|t|^3$. Their arguments, continuously lifted from zero, therefore give the phase bound $2(n+2\nu)x|t|^3$. At $x_0=4d/n$ its coefficient is at most $65d/8<9d$. The linear decrease in units of $\pi$ at $x_0$ is at least $15/4-6d/n\ge117/32>3.65$, while the phase error in the same units is at most $9\pi^2/d^2$. The level $T-3$ lies strictly between the limiting phase at zero and the phase at $x_0$. Since $D-2>T-3$ and $D-1<T$, both claimed levels occur. No phase monotonicity is needed.

At any such crossing in the chosen interval, dropping the subtractive weighted mean in the upper estimate gives
$$
T-k\le\frac{nx}{d}\left[\frac{129}{128}\left(\frac{16}{15}\right)^2+
2\frac{65}{64}\frac{\pi^2}{d^2}\right].
$$
The bracket is at most $376631/307200<5/4$ by $d\ge16$ and $\pi^2<10$. The lower bound $T-k\ge1$ gives $nx\ge4d/5$.

For every retained odd label $|\ell|\le d^{2/3}/8$ the angle has magnitude below one. The error from subtracting $\ell\Theta(\pi/d)$ is at most $18\pi^3/512<\pi/2$. This applies to either sign of $\ell$, so every retained term reinforces the sign of one principal term. Exactly $d$ odd residue classes occur in the chosen interval. When $d$ is odd, $t=\pi$ represents its own conjugate label and is discarded. When $d$ is even, neither endpoint is an odd label.

For either law, the independent-copy cosine identity and $1-\cos(jt)\le j^2(1-\cos t)$ bound the loss in squared modulus by $8x(1-\cos t)$. Both moduli exceed $3/4$, so the negative log loss is at most $8x(1-\cos t)$. The two atoms at zero and one in the first law give the opposite log bound $(15/16)^2x(1-\cos t)$. Combining these with $\nu/n\le1/128$ gives the stated coefficient $3/4$ in the exponential upper bound for $A(t)$. For the principal lower bound, $(n+\nu)x\le4d(129/128)$ implies $\log A(\pi/d)\ge-20\pi^2/d$. After using $nx\ge4d/5$ and the chord bound, the omitted magnitude at each discarded label is at most $\exp(-6\ell^2/(5d))$. The total is therefore at most $d\exp(-3d^{1/3}/160)<1/2$. At $d=10^{12}$ the negative exponent has magnitude $187.5$, and $\log(2d)/d^{1/3}$ decreases for all larger $d$. The principal magnitude exceeds $1/2$, proving strictness.

## Rational probes

The script uses the rational upper angle $22\ell/(7d)$ to bound the centered phase error. Both deficit laws are stochastically decreasing as the occupied tilt increases, because their weights acquire a decreasing geometric factor in $j$. Thus their raw moments and the script's rational error envelopes decrease from the reported lower witness tilt onwards. The true upper bound on the principal phase at that tilt, together with its limit $T$, certifies a crossing further along the same interval. The upper error for $\ell\ge3$ plus $\ell$ times the principal bound is strictly below $3/2<\pi/2$ for every retained label. This establishes the claimed phase alignment. The bracket search selects witnesses. A failed certificate does not certify absence of a crossing or a maximal witness.

A temporary-copy replay generated 51 records, of which 32 certified a crossing with a total of 96 retained positive labels. The script directly bounds the continuously lifted phases. As an additional exact check for the Gaussian branch in these finite probes, I bounded $|\arg G-\arg F|$ by the larger of the two means at the lower witness tilt times the rational upper angle, plus the two centered phase errors. This bound was below $3/4$ on every retained label. Thus the actual Gaussian branch agrees on these labels. The probe establishes no estimate for discarded finite-probe labels or for the full integral.

For clarity, the written estimate could include the explicit branch inequality, and the script could explain why lower-tilt moment bounds apply at any later crossing. These are presentation corrections. The reviewed conclusion remains a supporting analytic estimate.

**Signed** — Independent mathematical reviewer, agent-assisted.
