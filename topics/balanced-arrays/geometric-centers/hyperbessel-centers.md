# Exact signs at limiting geometric centers

The [certificate data](hyperbessel-centers.json) give every sign of $E_d(z)=\sum_{j\ge0}z^j/(j!)^d$ at $z=-[k(k+1)]^{d/2}$ for $2\le d\le10$, $1\le k\le50$. A reversal from $(-1)^k$ defeats this sufficient geometric-center test.

| $d$ | Positive | Negative | Agreement | Reversal | Largest final index |
|---|---:|---:|---:|---:|---:|
| 2 | 24 | 26 | 27 | 23 | 135 |
| 3 | 25 | 25 | 26 | 24 | 108 |
| 4 | 24 | 26 | 25 | 25 | 92 |
| 5 | 24 | 26 | 23 | 27 | 84 |
| 6 | 25 | 25 | 28 | 22 | 77 |
| 7 | 25 | 25 | 20 | 30 | 73 |
| 8 | 24 | 26 | 21 | 29 | 70 |
| 9 | 25 | 25 | 26 | 24 | 68 |
| 10 | 25 | 25 | 32 | 18 | 66 |

The run took 0.09 seconds and certified 450 nonzero signs with 222 reversals. Each row is a finite sample of 50 centers.

## Exact certificate and reproduction

Put $Q=[k(k+1)]^d$ and let $S_j$ be the partial sum through index $j$. Write $(j!)^dS_j=U_j-\sqrt Q\thinspace V_j$ with nonnegative integers $U_j,V_j$. At each step multiply both entries by $j^d$, then add $Q^{j/2}$ to $U_j$ for even $j$ or $Q^{(j-1)/2}$ to $V_j$ for odd $j$. Start with $(1,0)$. Since the conjugate factor is positive, the sign is that of $U_j^2-QV_j^2$. This also handles square $Q$.

The absolute term ratio from $i$ to $i+1$ is $(\sqrt{k(k+1)}/(i+1))^d<1$ for $i\ge k$. At $j>k$ the alternating tail brackets the whole sum between $S_{j-1}$ and $S_j$. Stop at the first pair with equal nonzero signs. The default reports an error if 2,000 terms do not suffice. Each record gives $d,k,Q$, the final index, and the observed and expected signs. Independent direct rational summation confirmed all 900 bracketing endpoints.

With Python 3 and no external dependencies, run from this directory.

~~~sh
python3 certify-hyperbessel-centers.py > reproduced-hyperbessel-centers.json
cmp hyperbessel-centers.json reproduced-hyperbessel-centers.json
~~~

## Density for fixed dimension

Put $y=\sqrt{k(k+1)}$. For $d=2$, the power series gives $E_2(-y^2)=J_0(2y)$. The fixed-order expansion gives

$$
E_2(-y^2)=(\pi y)^{-1/2}\bigl(\cos(2y-\pi/4)+O(y^{-1})\bigr).
$$

[DLMF 10.2.2, power series](https://dlmf.nist.gov/10.2.E2) · [DLMF 10.17.3, fixed-order expansion](https://dlmf.nist.gov/10.17.E3)

For $d\ge3$, the series is $`{}_0F_{d-1}(-;1,\ldots,1;-y^d)`$. In the two-exponential expansion of DLMF 16.11.9 set $p=0$, $q=d-1$ and $z=y^d$. Its parameters are $\kappa=d$ and $\nu=-(d-1)/2$. The gamma factors equal one and each series has leading coefficient one. The phases before taking roots of order $d$ are $\pm\pi$. Hence

$$
E_d(-y^d)=
\frac{2y^{-(d-1)/2}}{\sqrt d\thinspace (2\pi)^{(d-1)/2}}
e^{dy\cos(\pi/d)}
\left(\cos\left(dy\sin(\pi/d)-\frac{(d-1)\pi}{2d}\right)
+O(y^{-1})\right).
$$

The error inside parentheses is additive. The formula agrees with the $d=2$ specialization. [DLMF 16.11.1–16.11.4](https://dlmf.nist.gov/16.11.i) · [DLMF 16.11.9](https://dlmf.nist.gov/16.11.E9)

Since $y=k+1/2+O(k^{-1})$, the phase equals $\omega_dk+b_d+O(k^{-1})$ with $\omega_d=d\sin(\pi/d)$. The numerator $\omega_d$ is nonzero and algebraic, so $\omega_d/(2\pi)$ is irrational. The phase and the phase shifted by $\pi k$ are each equidistributed modulo $2\pi$. Away from the set where the leading cosine has absolute value at most $u$, any fixed $u>0$, the error preserves its sign for all sufficiently large $k$. The excluded set has limiting density tending to zero as $u\downarrow0$. Therefore for every fixed $d\ge2$ each raw sign has natural density one half. Agreement and reversal against $(-1)^k$ likewise each have density one half.

At full rank, $a_j=\binom nj^d$. For fixed $d,k$, $n^d\sqrt{a_{k-1}/a_{k+1}}\to[k(k+1)]^{d/2}$. The finite polynomial at its negative geometric center converges to the displayed entire-function value by termwise convergence and domination using $\binom nj\le n^j/j!$. Choose a reversing $k$ for each $d$ and take $n$ sufficiently large for the sign to persist, with $n\ge d^2$. This yields a sequence with $d\to\infty$ and $d/n\to0$ where the finite full-rank geometric-center test fails. This concerns the sign test and leaves the root claim intact.

## Prior-work screen

Checked 26 November 2026. General searches combined hyper-Bessel, geometric centers, hypergeometric zeros and sign density. The queries included `"Bessel" "sqrt{k(k+1)}" equidistribution signs` and `"hyper-Bessel" "zeros" asymptotic 0Fq Wright negative real axis`. No source directly treating the sampled signs or parity comparison surfaced. The density statement is a consequence of the classical asymptotics and irrational rotation. Related work locates zeros on rays and studies their distribution. [Chaggara and Ben Romdhane](https://doi.org/10.1080/10652469.2014.973191) · [Baricz and Singh](https://arxiv.org/abs/1702.00626)

GitHub and X/Twitter domain queries combined `"hyper-Bessel"` or `"0Fq"` with `"sign pattern"` or `"geometric centers"`. The GitHub repository query `"hyper-Bessel" "geometric center"` returned no candidates. Direct X exact-name and alias searches returned HTTP 200 with the generic application shell and no visible posts. Public index coverage limits the check.
