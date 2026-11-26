# Lower-height common-circle criteria

For $n\ge10{,}000$ and $k\ge400$, the existing sufficient inequality $0.89n/k>47+2.5\log n$ implies that $E_{n,k}/t$ and $E_{n+1,k}/t$ have simple negative roots and strictly interlace. For $4\le k\le399$ the same conclusion holds for every $n\ge55{,}000$. The previously reviewed $k=3$ theorem applies at all sizes. The argument concerns the actual next row.

Use the same $s,\theta,r,S,z_p,G,H,Y_j,\gamma,\Psi$ as the [wider-circle proof](../radial-taylor.md), and use its exterior theorem and coefficient contour identity. The [short-cycle proof](../effective-uniform.md) gives the bound $|G|\le6+10\log k$ on the disk of radius $r(1+1/(50k))$, the vertical gamma-density estimate for $H'$, and the phase-crossing argument. Numerical inequalities below are checked by rational enclosures of the elementary functions.

## Phase crossing for $n\ge10{,}000$

Let $h=\lfloor .35\sqrt n\rfloor$ and $\theta_*=(h+5/6)\pi/n$. We have $.34\sqrt n<h+5/6<h+1\le .36\sqrt n$ and $\theta_*<.012$. Sine and cosine bounds give $n\sin^2\theta_*>1$ and $s_*=\pi\cot\theta_*>2\sqrt n$. If $|\gamma(\theta_*)|<.48$ then $\Psi(\theta_*)<(h+1)\pi$, since $.48+.012<\pi/6$. By convexity of $x\mapsto1/(h+x)$,

$$
\log(1+1/h)-\frac1{h+5/6}
\ge\frac1{h+1/2}-\frac1{h+5/6}
>\frac1{3(h+1)^2}.
$$

Multiplying by $n$ gives more than $2.5>\log(459/40)$. Hence the exterior bound $|t_h|<(459/40)(h/(h+1))^n$ puts all $h$ exterior roots before $t(\theta_*)$ in modulus. At $s=0$, the identity $\gamma=\pi/2$ is unchanged, so $\Psi(\pi/2)=n\pi/2$. Given the two common-residue inequalities on $nS^2\ge1$, the previous first-hit, reciprocity and degree argument now applies throughout $n\ge10{,}000$.

For $k\ge400$, the wider-circle proof gives those two inequalities from $0.89n/k>47+2.5\log n$ throughout this range. Its remaining outer-endpoint requirement was $s_*>4\sqrt k$. This follows from $s_*>2\sqrt n$, since the sufficient inequality implies $n>4k$. The rational replay locates the first size satisfying the inequality for $k=400$ at $n=32{,}808$.

## A variable contour for $4\le k\le139$

Let $R_*=r(1+\alpha/k)$ and take $R$ in $[r(1+.9\alpha/k),R_*]$ away from the pole radii by $\delta=\min(\alpha r/(40k),1/r)$. This interval has length at least $4\delta$, and distinct pole radii whose $\delta$-neighborhoods meet it differ by more than $2\delta$: the difference of their squared radii is at least $8\pi^2$ and their sum is at most $2(R_*+\delta)<4r$. The denominator bound from the wider-circle proof gives $|1+e^{w-s}|^{-1}\le4/\delta$ at radius $R$. Polynomial growth from the original disk yields $|G|\le e^\alpha(6+10\log k)$ at $|w|\le R_*$. Use the indicated constants $L,\eta$ to bound the normalized circle error for either row by $340n\exp(L-\eta n/k)$.

| $k$ | $\alpha$ | $\beta$ | $\eta$ | $L$ |
| --- | ---: | ---: | ---: | ---: |
| $4$–$39$ | $.25$ | $10$ | $.218$ | $119$ |
| $40$–$80$ | $.4$ | $9$ | $.358$ | $150$ |
| $81$–$139$ | $.75$ | $7$ | $.672$ | $238$ |

Indeed $2e^\alpha(6+10\log k)<L$, $k\log(1+.9\alpha/k)>\eta$, and $2r/\delta\le 2(40k/\alpha+r^2)\le340n$. The check at $n=55{,}000$ gives $\eta n/k>L+11+1.5\log n$ in each slab, and the difference grows thereafter. Since $e^{11}>34{,}000$ and $S\ge n^{-1/2}$, the circle error is below $S/100$.

For $s\le\beta\sqrt k$, there are no nonprincipal poles inside $R_*$ because the increase in squared radius is at most $(\beta^2 k+\pi^2)(2\alpha/k+\alpha^2/k^2)<8\pi^2$. This upper bound decreases with $k$ in each slab. For $s>\beta\sqrt k$, the vertical segments satisfy $k\log(|w|/s)\le\alpha+\pi^2/(2\beta^2)$. For $k\ge21$, apply the gamma-density sum bound

$$
\pi |H'(w)|\le \pi e^{\alpha+\pi^2/(2\beta^2)}
\left(\frac{1}{\beta\sqrt k}+\frac1{\sqrt{2\pi(k-1)}}\right)<.48.
$$

The expression decreases within each slab. For $4\le k\le20$, we have $s>10\sqrt k\ge2(k-1)$ and $s>20$. The Poisson lower-tail bound at half the mean gives $\pi |H'(w)|\le\pi e^{.3}/(e^{2.5}-1)<.4$. This sharper bound compensates for the larger relative radius at these small thresholds.

## A variable Taylor split for $140\le k\le399$

Use $\alpha=1$ and $\beta=6$. The no-extra-pole bound and the gamma-density estimate above hold for this slab as well. Use the [Taylor contraction](../radial-taylor.md#the-truncated-logarithm) to improve the circle amplitude estimate. For $s\le6\sqrt k$ its small-$s$ formula applies with $U=1/(S\sqrt k)<1.92$ and gives the sum of two errors below 45. In detail the formula gives $12/k+(e+1)(2+4.5U)+.76(2+2.25U)$. The factor $.38$ in each contracted tail is still valid for $k\ge140$ because $k(1-e^{-1/k})\ge1-1/(2k)$.

For $s>6\sqrt k$, use $r/s<1.001$, $r-s<.138s/k$, $R_*-s<1.14s/k$ and $s-(1-1/k)r>.862s/k$. In the radial-change bound split the exponential frequencies at $a=7k/(5s)$. Below the split the bounds are $2(1.001)(7/5)e^{1.14\cdot7/5}<14$ at the wider radius and $(1.001)(7/5)e^{.138\cdot7/5}<2$ at the principal radius. Above the split the Poisson mean exceeds $7k/5$ at each comparison radius, so the lower-tail bound at $5/7$ of the mean gives decay at least $.045$ times the mean. As $.045-1.14/140>1/30$, the remaining radial cost at either radius is at most $60r/(ks)<.43$. The contracted Taylor tails cost less than $3.1$ at each radius by the same upper-tail split as in the wider-circle proof, using $2/.862<3$ and $(1+\log k)e^{-k/6}<.1$ for $k\ge140$. These six costs also total less than 45. The contracted real-part comparison thus gives amplitude ratio less than $13k e^{45}$. The associated two circle errors are at most $1300 n^2 e^{45-.89n/k}<S/100$, by $.89n/k>58+2.5\log n$. The latter holds at $n=55{,}000$, $k=399$, and remains true at smaller $k$ in the slab and larger $n$.

## Common residue signs in all four slabs

For $k\ge21$ every enclosed pole has $u=(p^2-1)S^2\le(1+\alpha/k)^2-1<.04$, and so $|z_p|^n\le e^{-.49(p^2-1)}$ by $\log(1+u)\ge u-u^2/2$ and $nS^2\ge1$. The gamma estimate bounds its amplitude ratio to the principal pole by $e^{.48(p+1)}$. For $k\le20$ use $u<.13$ and hence the decay constant $.46$, with amplitude ratio bounded by $e^{.4(p+1)}$. In either case the weighted sum over the nonprincipal positive odd poles is below $.42$, retaining $p=3$ separately and bounding the remaining terms by $5e^{-24a}+\frac12\int_5^{\infty}u e^{-a(u^2-1)}\,du$ for $a=\text{decay}-\text{amplitude}/4$. Subtracting the two common-residue sums multiplies each pole term by $z_p-C$, with modulus at most $pS$. Together with the two circle errors below $S/100$, this gives the required simultaneous inequalities $|Y_n-\cos\Psi|<1/2$ and $|Y_{n+1}-CY_n+S\sin\Psi|<S/2$. At the outer endpoint $s_*>2\sqrt n>\beta\sqrt k$ in every slab, so the required phase bound there holds. The first-hit argument then establishes the claim.

Run `python3 -I -B check.py` for the scalar checks. The checker sums positive Taylor series with a geometric remainder for exponentials, and uses a positive atanh series after extracting factors of two for logarithms. No polynomial roots are computed and no Lean or Rocq verification is claimed.

[Recorded output](output.txt) · [Independent review](review.md) · [Independent checker](check-independent.py) · [Independent output](independent-output.txt)

Run the independent replay with `python3 -I -B check-independent.py`.
