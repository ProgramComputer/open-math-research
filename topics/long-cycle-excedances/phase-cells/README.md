# The principal phase at a minimum cycle length

Let $`E_{n,k}`$ enumerate permutations of $`[n]`$ whose cycles all have length at least $`k`$, weighted by strict excedances. Write $`x=\pi\cot\theta`$, $`S=\sin\theta`$, $`w=x+i\pi`$ and $`t=-e^{-x}`$, for $`0\lt \theta\le\pi/2`$. The finite log tilt $`G_{k,x}`$ and the phase $`\Psi_n=(n+1)\theta-\mathrm{Im} G_{k,x}(w)`$ are those of the [original-row coefficient identity](../fixed-threshold.md).

**Phase derivative.** For $`n\ge k\ge7`$ the principal phase is strictly increasing on the entire middle interval $`n\sin^2\theta\ge1`$. In its interior it satisfies

$$
\left|\Psi'_n(\theta)-n\right| < \frac{32}{35}n.
$$

**Explicit angular cells.** For $`k\ge7`$ and $`\pi/6\le\theta\le\pi/2`$ one has $`|\Psi_n-n\theta|<1/2`$ for every $`n`$. If also $`n\ge100k\log k`$, every complete cell $`[j\pi/n,(j+1)\pi/n]`$ inside this band contains a zero of $`E_{n,k}(-e^{-\pi\cot\theta})`$ in its interior. At *every* old zero in that cell the literal upper-row sign is $`(-1)^{j+1}`$. Thus there are at least $`\lfloor n/2\rfloor-\lceil n/6\rceil`$ distinct old zeros in these open cells. This statement counts one witness per cell. Its proof does not require an assumption about the locations of the other roots.

The derivative estimate gives an invertible phase coordinate on the full middle interval. The cell statement additionally locates witnesses at named grid ranks in the range where the repository has a quantitative bound for the actual row. [Alexandersson’s original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjLongCycleExcedances) · [Common coefficient expansion](../lean/common-pin/RepositoryCoherentPoles.lean) · [High-angle sign and error estimate](https://github.com/ProgramComputer/open-math-research/pull/265)

**Formal coverage.** The generic Eulerian derivative, cancellation, positive lattice bound and trigonometric sign tests compiled on the shared Lean 4.19.0 research pin. The original-row specialization on the common Lean 4.33.1 pin is under verification. [Derivative](TiltDerivative.lean) · [Lattice bound](SeventhMoment.lean) · [Cell signs](GridSigns.lean) · [Original-row specialization](ActualPhaseDerivative.lean) · [Independent mathematical review](independent-review.md)

## Proof of the derivative formula

Let $`A_m(t)`$ be the ordinary Eulerian descent polynomial with $`A_0=1`$. For $`j\ge1`$ put

$$
g_j(x)=-\frac{t A_{j-1}(t)}{j!(1-t)^j},\quad
G_{k,x}(z)=\sum_{j=1}^{k-1}g_j(x) z^j,\qquad
\gamma(\theta)=\mathrm{Im} G_{k,x}(w).
$$

In particular $`g_1=-t/(1-t)`$. Eulerian insertion gives $`A_{m+1}=(1+mt)A_m+t(1-t)A_m'`$. Differentiate $`tA_m/(1-t)^{m+1}`$ with respect to $`t`$ to obtain $`A_{m+1}/(1-t)^{m+2}`$. Since $`dt/dx=-t`$, it follows that $`g'_j=-(j+1)g_{j+1}`$. With $`dw/dx=1`$, all interior terms cancel:

$$
\frac{d}{dx}G_{k,x}(w)=g_1-k g_k w^{k-1}.
$$

For each odd integer $`p`$ set $`w_p=x+ip\pi`$ and $`\rho_p=|w/w_p|`$. The [Eulerian pole expansion](../lean/common-pin/RepositoryPoleProfile.lean) gives $`-k g_k=\sum_p w_p^{-k}`$. This series converges absolutely. The term $`p=1`$ in $`w^{k-1}\sum_p w_p^{-k}`$ is $`1/w`$, whose imaginary part is $`d\theta/dx`$. The linear coefficient $`g_1`$ is real. Using $`dx/d\theta=-|w|/S`$ gives the exact identity

$$
(\gamma-\theta)'(\theta)
=-\frac1S\mathrm{Im}\left(e^{-i\theta}\sum_{p\ne1}(w/w_p)^k\right).
$$

Only the single coefficient of order $`k`$ enters here. No termwise differentiation of the pole series is required. At $`x=0`$, one has $`\gamma=\theta=\pi/2`$. Indeed all odd $`g_j`$ for $`j\ge3`$ vanish at $`x=0`$ by pairing $`p`$ with $`-p`$, the even powers of $`w=i\pi`$ are real, and $`g_1=1/2`$.

## Monotonicity on the whole middle interval

The conjugate pole $`p=-1`$ has modulus ratio one. For $`p=\pm(2h+1)`$ with integer $`h\ge1`$, the squared ratio is exactly $`1/(1+4h(h+1)S^2)`$. Since $`k\ge7`$, the two far half-lattices give

$$
\sum_{|p|\ge3}\rho_p^k
\le 2\sum_{h\ge1}(1+4h^2 S^2)^{-7/2}
\le \frac{1}{S}\int_0^\infty (1+u^2)^{-7/2}\mathrm{d}u
=\frac{8}{15S}.
$$

The middle inequality bounds each right-endpoint value by the average on the preceding interval of length $`2S`$. With $`v=u/\sqrt{1+u^2}`$, the integral becomes $`\int_0^1(1-v^2)^2\mathrm{d}v=8/15`$. Consequently $`|\Psi'_n-n|\le1/S+8/(15S^2)`$. If $`nS^2\ge1`$ then $`1/(nS)\le1/\sqrt n\le1/\sqrt7\lt 8/21`$, and $`8/(15nS^2)\le8/15`$. Their sum is less than $`32/35`$. Continuity gives strict monotonicity up to the endpoints.

## High-angle displacement

In the identity for $`(\gamma-\theta)'`$, the $`p=-1`$ summand is exactly $`-\sin((2k-1)\theta)/\sin\theta`$. In this band the far poles have $`\rho_p\le1/\sqrt3\lt3/5`$. Also $`\sum_{|p|\ge3}\rho_p^2\le2`$, since $`\rho_p^2\le4/(p^2-1)`$ and $`\sum_{h\ge1}1/(4h(h+1))=1/4`$ on each half-lattice. Integrate from $`\theta`$ to $`\pi/2`$. For $`m=2k-1`$, integration by parts bounds the contribution of the conjugate pole by $`(2\csc\theta-1)/m\le3/m`$, using $`\cos(m\pi/2)=0`$ and the decrease of $`\csc`$ on this interval. The absolute contribution of the far poles is at most $`2(3/5)^{k-2}\int_{\pi/6}^{\pi/2}\csc v\mathrm{d}v`$. Bounding $`\csc v`$ by 2 up to $`\pi/4`$ and by $`3/2`$ thereafter bounds the integral by $`13\pi/24`$. Thus

$$
|\gamma-\theta|\le \frac3{2k-1}+\frac{13\pi}{12}(3/5)^{k-2}
\le \frac3{13}+\frac{13}{12}\frac{22}7(3/5)^5 < \frac12.
$$

## Actual old and new signs

In the stated large-size range the [actual high-angle estimate](https://github.com/ProgramComputer/open-math-research/pull/265) gives $`|Y_n-\cos\Psi_n|\le1/6`$, where $`Y_n`$ is a positive multiple of $`E_{n,k}(t)`$. At an old zero it gives the sign of the literal row $`E_{n+1,k}(t)`$ as the sign of $`-\sin\Psi_n`$. The phase convention follows from $`w/|w|=e^{i\theta}`$ and $`\exp G_{k,x}(w)/|\exp G_{k,x}(w)|=e^{i\gamma}`$.

At a grid endpoint $`n\theta=j\pi`$, the signed cosine is at least $`1-(1/2)^2/2=7/8`$, by the displacement estimate. The actual old sign is therefore $`(-1)^j`$. Consecutive endpoints have opposite signs, so continuity supplies at least one interior root. At any such root, $`|\cos\Psi_n|\le1/6`$. The phase is within one half of $`[j\pi,(j+1)\pi]`$. If it were outside this open interval it would be within one half of an endpoint, forcing $`|\cos\Psi_n|\ge7/8`$. Hence $`\sin\Psi_n`$ has sign $`(-1)^j`$, giving the claimed upper-row sign. Dividing each row by the common variable at $`t<0`$ reverses its displayed sign.
