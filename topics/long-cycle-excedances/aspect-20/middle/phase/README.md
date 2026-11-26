# Vertical phase and enclosed residues at old sizes 251 through 9999

Let $251\le n<10{,}000$, $k\ge4$, $n/k\ge20$, $s\ge0$,
$r^2=s^2+\pi^2$, $S=\pi/r$, and $w_p=s+ip\pi$ for odd $p$.
Assume $nS^2\ge1$ and $R\le (1+3/k)r$. For the numerator
$T_s=e^{G_s}$ of the common-circle coefficient formula, the
weighted sum over all enclosed positive nonprincipal poles satisfies

$$
\sum_{\substack{p\ge3\text{ odd},\quad |w_p|\le R}}
p\left(\frac r{|w_p|}\right)^{n+1}
\left|\frac{T_s(w_p)}{T_s(w_1)}\right| < \frac1{10}.
$$

The bound includes poles at the limiting radius, so it applies to
every allowed choice of pole-avoiding circle. It gives the same
bound on the nonprincipal contribution to the common-residue
contrast after division by $S$, since $|z_p-C|\le pS$. The
unweighted contribution to the old row is below $1/30$. Circle
integration errors are a separate input.

## Interval estimate

Put $m=k-1$ and $a_k=6/k+9/k^2$. A nonprincipal pole can be
enclosed only if $p^2-1\le a_k(1+s^2/\pi^2)$. Since
$a_k\le33/16$, this excludes all such poles for $s\le5$.
In particular no logarithm at $s=0$ is needed. The inequality
$nS^2\ge1$ gives $s<315$ at the top size. The enclosure
condition also gives $p<145$.

For $s>0$, the established expansion at the odd poles is
$G_s(w_p)=-\log(1+e^{-s})-H(w_p)$ with

$$
H(w)=\sum_{a\ge1}\frac{e^{-aw}}{a}
\sum_{j=0}^{m}\frac{(aw)^j}{j!}.
$$

Differentiation cancels all terms except the highest power.
The exponential series and its derivative converge locally
on $\Re w>0$. With $D_m(s)=\sum_{a\ge1} e^{-as}(as)^m/m!$,

$$
|H'(s+iy)|\le D_m(s)(1+y^2/s^2)^{m/2}.
$$

Integrate between $w_1$ and $w_p$ on the vertical segment,
of length $\pi(p-1)$. The real part of $H(w_1)-H(w_p)$ is
therefore at most $\pi(p-1)D_m(s)(1+p^2\pi^2/s^2)^{m/2}$.
This yields the required exponential bound on the numerator ratio.

For an integer box $s\in[l,h]\subset[5,315]$, let
$P=157/50<\pi<Q=22/7$. Use only odd $p\ge3$ with
$p^2-1\le a_k(1+h^2/P^2)$. For a density term at frequency
$a$ maximize $e^{-t}t^m/m!$ at $t=m$ clipped to $[al,ah]$.
For frequencies $a\ge A=\max(1,\lceil2m/l\rceil,\lceil180/l\rceil)$,
use the Poisson lower tail at half the mean. This gives
$e^{-as}(as)^m/m!\le e^{-al/8}$, and the remaining sum is
geometric. Call the total bound $D$.

Put $n_0=\max(251,20k,1+l^2/Q^2)$ and
$u=(p^2-1)P^2/(P^2+h^2)$. The logarithm of the radial power is
at most $-(n_0+1)\log(1+u)/2$. The upper bound
$(1+3/k)^2(1+\pi^2/s^2)$ on $|w_p|^2/s^2$ supplies a second
choice for the vertical factor. Thus the upper bound on the
summand in the displayed result is

$$
p\exp\left[-\frac{n_0+1}{2}\log(1+u)
+Q(p-1)D(1+b)^{m/2}\right],
\qquad
b=\min\left(\frac{p^2Q^2}{l^2},
(1+a_k)(1+Q^2/l^2)-1\right).
$$

The checker evaluates these upper bounds with rigorous Arb
enclosures. Each strict inequality compares the upper end
of the enclosed bound with the claimed cap. The integer
boxes cover the whole continuous angle range after the
analytic exclusions. The bound uses the lower size allowed
at each box, so it applies simultaneously to all integers
$n$ without testing individual angles or row sizes.

## Exterior phase join

This part applies to all $n\ge251$ when $n/k\ge20$.
Let $H_0=\lfloor7\sqrt n/20\rfloor$ and
$\theta_{\ast}=(H_0+5/6)\pi/n$. Using $\sqrt n>15$, its phase numerator
$H_0+5/6$ lies between $(61/180)\sqrt n$ and $(73/180)\sqrt n$.
The elementary sine and cosine Taylor inequalities give
$\theta_{\ast}<.086$, $n\sin^2\theta_{\ast}>1$ and
$s_{\ast}=\pi\cot\theta_{\ast}>(12/5)\sqrt n>38$.
On the segment from $s_{\ast}$ to $s_{\ast}+i\pi$,

$$
k\log\frac{|s_{\ast}+iy|}{s_{\ast}}\le\frac{k\pi^2}{2s_{\ast}^2}<.043.
$$

For $k\ge25$, unimodality and mesh spacing give
$D_{k-1}(s_{\ast})\le1/s_{\ast}+1/\sqrt{2\pi(k-1)}<1/38+1/12$.
Precisely, omit a largest mesh value and charge every other
term to the integral over the interval toward the mode.
The omitted term is at most the gamma density maximum
$1/\sqrt{2\pi(k-1)}$ by Stirling's inequality. Consequently
$|\gamma(\theta_{\ast})|=|\Im G_{s_{\ast}}(s_{\ast}+i\pi)|<.37$.
For $4\le k\le24$, use $m\le23<(5/8)s_{\ast}$ and the Poisson
lower-tail exponent $1-5/8+(5/8)\log(5/8)>.08$. The density
sum is at most $1/(e^{.08\cdot38}-1)$, giving $|\gamma|<.18$.
In both cases $|\gamma|+\theta_{\ast}<\pi/6$, as required for the
initial common-residue phase to lie below $(H_0+1)\pi$.

## Replay

With python-flint 0.9.0 and FLINT 3.6.0, run `python check.py`.
The completed default replay checks 32,859 continuous
boxes and 170,560 pole bounds in under four seconds.
[Recorded output](output.txt)

A tighter replay, `python check.py --step 1 --cap 2/25`,
checks 129,687 boxes and 666,005 pole bounds and certifies
the upper bound $2/25$ in place of $1/10$.
[Tighter replay output](output-tight.txt)
