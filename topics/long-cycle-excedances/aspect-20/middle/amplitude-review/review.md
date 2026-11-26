# Independent review of the low-height circle amplitude bound

November 26, 2026. This agent-assisted review checks the common-circle amplitude and error bound at old sizes $251\le n\le9999$, $k\ge4$, $n/k\ge20$, and $n\sin^2\theta\ge1$. I reviewed the author's checker with SHA-256 `a4adfec0669712f8c24cf98285fe2a6fae76b665aac69a9506e8361e29a17ab2` and independently reproduced the stated bound $|e_N|<S/100$ for $N=n,n+1$. The alternate certificate also verifies $|e_N|<S/4000$ using finer partitions and a stronger elementary denominator estimate. This review covers the circle amplitude and errors. The residue, phase and root-count arguments use separate inputs.

## Common normalization and Cauchy error

Set $w_p=s+ip\pi$, $r=|w_1|$, $S=\pi/r$, $T_s=e^{G_s}$ and $f=T_s/(1+e^{w-s})$. The residue contribution to the normalized old or new row comes from $[w^N]f$. On a radius $R$ avoiding the poles, the remaining circle integral is bounded by $R^{-N}\Vert f\Vert_{\infty}$. The row normalization is

$$
Y_N=\frac{r^{N+1}E_{N,k}(t)}{2|T_s(w_1)|N!(1-t)^{N+1}},
\qquad t=-e^{-s}.
$$

It follows from the coefficient identity, with the same $T_s(w_1)$ and parameters for both rows, that

$$
\frac{|e_N|}{S}
\le \frac{r^2}{2\pi}\left(\frac rR\right)^N
\sup_{|w|=R}\frac{|T_s(w)/T_s(w_1)|}{|1+e^{w-s}|}.
$$

The radius penalty uses $n$ in both rows, which is valid since $R>r$. This normalization gives the adjacent contrast error at most $(1+C)S/100\le S/50$ when $0\le C=\cos\theta\le1$ and either row uses the author's bound.

## Coefficient envelopes

For the degree $(k-1)$ Taylor truncation $G_s$ of $\log((1+e^{w-s})/(1+e^{-s}))$, the linear coefficient is exactly $1/(1+e^s)$. At degree $j\ge2$ the simple-pole expansion gives absolute coefficient at most $j^{-1}\sum_p |w_p|^{-j}$. This also holds at $s=0$, where the positive-frequency series is unnecessary. At $s\in[u,v]$, normalized to powers of $r$, replace each $r/|w_p|$ by its value at $v$, since $(s^2+\pi^2)/(s^2+p^2\pi^2)$ increases with $s$ for $|p|\ge1$. Beyond the last explicitly retained positive pole $p_0$, use

$$
\sum_{p=p_0+2,p_0+4,\ldots} (r/|w_p|)^j
\le (r/|w_{p_0}|)^{j-2}\frac{r^2}{2\pi^2p_0}.
$$

The mesh-two integral bounds the sum of $p^{-2}$, and the norm of the residual power decreases with $p$. The author uses $p_0=31$, and the independent replay uses $47$.

For $u>0$ a second valid coefficient majorant in units of $r^j$ is
$\sum_{a\ge1} e^{-au}(ar_v)^j/(a j!)$, where $r_v^2=v^2+\pi^2$. It follows from expanding the logarithm in exponential frequencies near the origin. For the omitted frequency tail after its first evaluated term, the ratio is at most $\exp(-u+(j-1)/a)\le e^{-u/2}$ whenever $au\ge2J$ and $j\le J$. The author's floating-point seed for a finite frequency index affects efficiency only. It checks the sufficient endpoint inequality before using that index. The independent replay selects the cutoff using an integer ceiling of an exact rational. Both use the better majorant where the two comparisons separate. At the smallest heights the pole bound is sufficient.

For a threshold group $K\le k\le L$, sum through degree $L-1$. Each degree contributes at most its normalized coefficient majorant times $1+(1+3/K)^j$ to $\Re(G_s(w)-G_s(w_1))$ on the entire allowed circle range. All terms in this majorant are nonnegative, so enlarging the degree and radius factors separately is valid.

## Radius and logistic denominator choices

If $1+8(\pi/r_v)^2>(1+4/K)^2$, the next pole radius is bigger than $(1+4/k)r$ uniformly in the group. Choosing $R=(1+3/k)r$ gives distance at least $r/k$ to every pole, including the principal pair. Otherwise subdivide the legal interval $[(1+2.7/k)r,(1+3/k)r]$ by its interior pole radii. Its length is $0.3r/k$, and there are at most $2+(1+3/K)r_v/(2\pi)$ gaps because any enclosed positive odd index $p$ satisfies $p\pi\le R$. The midpoint of a largest gap is separated from every pole radius by at least half that gap's length. This also applies to poles outside the interval, which lie beyond a boundary. Reverse triangle inequality converts this radial bound to distance at every point of the chosen circle.

For any distance lower bound $\delta\le1/2$, the logistic denominator admits the author's bound $|1+e^{w-s}|^{-1}\le 4/\delta$. The alternate replay uses $3/\delta$, justified as follows. Let $u_0=\Re(w-s)$ and let $y$ be its imaginary displacement from the nearest odd multiple of $\pi$, so $u_0^2+y^2\ge\delta^2$, $|y|\le\pi$. If $|u_0|\ge\delta/2$, the denominator is at least $1-e^{-\delta/2}\ge7\delta/16$. Otherwise $|y|\ge\sqrt3\delta/2$ and the sine term in the squared modulus gives at least $\sqrt3 e^{-1/8}\delta/\pi>\delta/3$. In either radius branch, capping the physical gap at $1/2$ and inserting it into the Cauchy factor gives the claimed prefactors. For example, in the largest-gap branch the author's bound is

$$
\max\left(\frac{4r_v^2}{\pi},
\frac{40}{3}\frac{Lr_v}{\pi}\left(2+\frac{(1+3/K)r_v}{2\pi}\right)\right).
$$

## Full parameter coverage and replay

The lower size bounds are $n\ge251$, $n\ge1+u^2/\pi^2$, and $n\ge20k$. The first two yield the penalty using the weaker relative radius for $k=L$. For the third, $k\log(1+b/k)$ is increasing in $k$ for $b>0$, so its group lower bound is at $K$. These give separate lower bounds on the log radius penalty and may be maximized. All eligible $k$ run from 4 to 499, and $nS^2\ge1$ with $n\le9999$ forces $s<315$. The alternate grid explicitly includes $s=0$ and matches every integer threshold in its disjoint group cover.

I independently rechecked $n=251$ for $4\le k\le12$ and all eligible heights, using 1,350 height-threshold boxes. The full alternate run used 84 threshold groups and 945 height intervals. The author's run passed 38,430 boxes and recorded a worst log upper bound below $-6.60$. The alternate run passed 79,380 boxes and recorded a worst log upper bound below $-8.48$. The author replay and the independently coded enclosures both pass. Python-FLINT 0.9.0 with FLINT 3.6.0 was used.

[Author replay](primary-output.txt) · [Independent checker](check.py) · [Independent replay](independent-output.txt)
