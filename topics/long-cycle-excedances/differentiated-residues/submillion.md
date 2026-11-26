# A sub-million uniform interlacing cutoff

There are two independent steps. The first gives a differentiated common-residue comparison for $n/k\ge25$ in a wider angular range. The second checks the exterior entrance and the circle estimates down to old size $972{,}000$. Together with the [adaptive table](../adaptive-poles/README.md) and the [wide differentiated slab](README.md), they give strict consecutive interlacing with simple negative nonzero roots for every $3\le k\le n$ at all $n\ge972{,}000$. [Exact constants](check-submillion-residues.py) · [Replay](submillion-residues-output.txt) · [Independent review](review-submillion-residues.md) · [Independent checker](verify-submillion-independent.py) · [Independent output](submillion-residues-independent-output.txt)

## Differentiated comparison for $n/k\ge25$

Keep the notation and exact residue identities of the [wide differentiated proof](README.md). In this section assume

$$
n/k\ge25,\qquad A=kS\ge11,\qquad kS^2\le1/7,\qquad nS^2\ge6/5.
$$

Then $k\ge847$, $C>999/1000$, and $-\log C\le1/(13k)$. Put $m=n+1-k$. Both $N=n,m$ satisfy $X=N/k\ge24$, $NS^2\ge144/125$ and $NS\ge264$.

Use the degree weight $\omega=e^{13/(20k)}$. At $c=13/20+1/13$, the block bounds give

$$
\sum_s|b_s|e^{cs/k}<10/k,\qquad
\sum_s s|b_s|e^{cs/k}<27,\qquad
\sum_s\sqrt{s}|b_s|e^{cs/k}<16/\sqrt{k}.
$$

The checker bounds these by summing the first block total and the factorial envelope $1/(2j!k)$ for blocks $j\ge2$, then using Cauchy–Schwarz. The same envelope gives $\sum_{s>10k}|b_s|<1/(6{,}000{,}000k)$.

Use the coefficient majorants $D_+$ and $J_+$ of the wide proof. The bounds are $D_+(\omega)<D_{\mathrm{max}}=10/11$ and $J_+(\omega)\le27/N+16/(\sqrt k\,NS^2)+10/(kNS^2)$. The full signed linear logarithm has weighted norm at most $(\pi/2)D_{\mathrm{max}}$. Every individual factor $A_{a,q}$ has norm at most $D_{\mathrm{max}}/|q-a|$. Thus the higher logarithm terms have norm at most $D_{\mathrm{max}}^2/(2(1-D_{\mathrm{max}}/2))$, using $\sum_{q\ne a}|q-a|^{-2}<1$. The normalized derivative of the logarithm has an $a$-independent coefficient majorant with weighted sum at most $(\pi/2+D_{\mathrm{max}} /(1-D_{\mathrm{max}}/2))J_+(\omega)$. This follows by marking one factor for differentiation in every logarithm power. Exponentiating the log majorants gives common coefficientwise bounds for $Q_a$ and $Q_a'/N$ with weighted sums below nine and sixteen, respectively.

Retain $a=\pm1,\pm3$ in the common residue approximation $F_N=\sum_{a\mathrm{\ near}}M_a z_a^N+\mathcal E_N$. At these poles $\omega\rho_a\ge e^{11/(140k)}$. For $T\le N-10k$ the scalar difference between the actual $d_{N-T}$ and $d_\infty$ is below $1/(6{,}000{,}000k)$. The pole mass and first moment over this near set are bounded by four and eight. For $T>N-10k$, the value and derivative estimates from the degree split instead pay $e^{-(13/20)(X-10)}<1/8000$. In the differentiated distinguished factor, putting $v=T-(N-10k)$ and using the slack in $\omega\rho_a$ gives

$$
\frac{|N-T|}{N}e^{-11v/(140k)}
\le 10/X+140/(11eX)<5/8 .
$$

For the remaining poles $|a|\ge5$, split after differentiation according to whether $\rho_a^{-1}\le\omega$. The slower poles retain $\rho_a^N$, whose first moment beyond $|a|=3$ is below $1/20000$ by the power envelope at $NS^2\ge144/125$ and the integral from five. The faster poles retain $\rho_a^k e^{-(13/20)(X-1)}$. The same scalar pole bounds as before apply, and at $X=24$ the penalty is below $1/2{,}000{,}000$. Adding the near and far pieces gives

$$
k|\mathcal E_N|<6/1000,qquad
k|\mathcal E_N'|/N<17/1000 .
$$

As in the wider proof, $M_a'/(NM_a)=z_a/(NS)+\pi H'(w_a)/(NS^2)$. At $s=\pi C/S$ we have $s>8\sqrt k>232$ and $\log(|w|/s)<65/(100k)$ on the near vertical segments. The gamma-density estimate gives $\pi|H'(w)|<12/100$, so $|M_a'/(NM_a)|<11/100$. Also $H(s)\le1+\log(1+3k/(2s))+1/100$ from the harmonic sum and Poisson bound. It follows that $k|M_1|>e^{-113/100}11/(\pi+(33/2)/C)>17/100$. The normalized nonprincipal near amplitude is below $17/1000$ using $\rho_3^N<e^{-23/5}$ and $|M_3/M_1|\le e^{48/100}$. Its normalized derivative adds a factor at most $3+11/100$.

Consequently the total old value error, divided by $2|M_1|$, is below $35/1000$. At an old zero the principal sine has magnitude above $99/100$, since its cosine has magnitude below $35/1000$. The other derivative contributions cost at most $11/100+53/1000+(17/1000)/(34/100)$, so $|F'_n|/(2n|M_1|)>77/100$, with the sign of the derivative of the principal oscillation. At integer samples the phase differs from $n\theta$ by at most $\theta+12/100<14/100$, so these give the same alternating signs as the earlier middle arguments. In particular the principal sine at any old zero in the integer gap of index $j$ has sign $(-1)^j$.

Since $|F_m|/(2|M_1|)<1+35/1000$ and $|B_k|/(n S)\le(2/x+2/\sqrt x)/A$ where $x=n/k\ge25$, the normalized lag is below $5/100$. At an old zero the insertion identity gives

$$
(n+1)F_{n+1}=SF'_n+B_kF_m .
$$

This follows by multiplying the insertion recurrence for $E_{n+1,k}$ by $r_0^{n+1}/(n!(1-t)^{n+1})$, using $dt/d\theta=r_0t/S$ and the Eulerian cycle pole identity. Reversing the insertion sign changes the sign of $B_kF_m$ in these units. The derivative sign therefore determines both pencil signs at every old root in the new slab.

## The phase entrance below one million

Let $H=\lfloor7\sqrt n/20\rfloor$ and $\theta_{\mathrm{ent}}=(H+5/6)\pi/n$, for $n\ge972{,}000$. We have $H+5/6>(17/50)\sqrt n$ and $H+1\le(9/25)\sqrt n$. The sine and cosine Taylor inequalities at $\theta_{\mathrm{ent}}<1/100$ give

$$
n\sin^2\theta_{\mathrm{ent}}>11/10,\qquad s_{\mathrm{ent}}:=\pi\cot\theta_{\mathrm{ent}}>2\sqrt n .
$$

The general exterior theorem is valid here because $n\ge10{,}000$. Its last exterior root is smaller in modulus than the first phase point: using the theorem's coefficient scale and $H\ge9$,

$$
n\log(1+1/H)-\frac{n}{H+5/6}
\ge\frac{n}{(H+1)^2}
\left(\frac12-\frac{H+1}{6(H+5/6)}\right) >\frac{33/100}{(9/25)^2}>\frac52>\log((9/8)(51/5)).
$$

The comparison $\pi\cot\theta_{\mathrm{ent}}<n/(H+5/6)$ then gives the claimed ordering. Wherever $|\gamma|<12/25$ at this endpoint, the usual phase $\Psi=(n+1)\theta-\gamma$ starts below $(H+1)\pi$ because $12/25+1/100<\pi/6$. The endpoint at $\pi/2$ and the [phase crossing count][short] are unchanged.

## Extending both circle criteria

For $k\ge400$, the [wider-circle proof][radial] gives the same local residue inequalities under $nS^2\ge1$ and $0.89n/k>47+2.5\log n$. Its Taylor estimate, circle radius choice and pole weights use these conditions and $k\ge400$. Its phase entrance applies below one million by the preceding paragraph: the ratio criterion implies $n>4k$, so $s_{\mathrm{ent}}>4\sqrt{k}$, as required for its bound on $\gamma$ there. Therefore the wider circle proves strict interlacing also for $n\ge972{,}000$ under its ratio criterion.

For $k=3$ use the all-size theorem. For $4\le k<400$ adapt the [small-threshold circle][small]. Its polynomial growth estimate still gives $|G(w)|<82$ on $|w|\le r_0(1+1/(5k))$. The radius-separation and inverse-denominator bounds are unchanged. Indeed the radial interval $[r_0(1+3/(20k)),r_0(1+1/(5k))]$ has length at least $4\delta$ for $\delta=\min(r_0/(80k),1/r_0)$, and pole radii near it are more than $2\delta$ apart by subtraction of their squares. The only altered power bound is $k\log(1+.15/k)>.146$ for $k\ge4$. This gives normalized remainder at most $2(80k+r_0^2)e^{164-.146 n/k}<S/100$. Indeed $80k+r_0^2<90n$ and $.146 n/400>164+10+1.5\log n$ at and above $972{,}000$, by its positive derivative difference there.

Switch at $s=10\sqrt k$. When $s\le10\sqrt k$, the outer increase of squared radius is at most $(100k+\pi^2)(2/(5k)+1/(25k^2))<8\pi^2$, so only the principal pair is enclosed. For $s>10\sqrt k$, the vertical segments satisfy $\log(|w|/s)<1/(4k)$. If $k\ge21$, the gamma density derivative bound is

$$
\pi|H'(w)|\le\pi e^{1/4}\left(1/(10\sqrt{21})+1/\sqrt{40\pi}\right)<12/25.
$$

If $4\le k\le20$, then $s>20$ and $s>2(k-1)$. Sum the Poisson lower-tail estimates for the gamma terms, giving $\pi|H'(w)|\le\pi e^{1/4}/(e^{5/2}-1)<12/25$. Each enclosed pole has $u=(p^2-1)S^2\le(1+1/(5k))^2-1\le41/400$. The stronger entrance $nS^2>11/10$ gives $\rho_p^n\le e^{-(49/100)(p^2-1)}$ because $\log(1+u)\ge(1-u/2)u$. The same weighted nonprincipal error $21/50$ and common-residue sign comparison follow. At the entrance $s_{\mathrm{ent}}>2\sqrt n>10\sqrt k$. The phase crossing proof therefore counts all roots and proves actual consecutive interlacing at the small thresholds down to $972{,}000$.

## Combining the ranges

It suffices to consider $972{,}000\le n<1{,}408{,}334$ by the wider differentiated result. The extended small-threshold criterion covers $k<400$. For $k\ge400$ the complete three-cycle theorem applies when $n/k<4$. The adaptive table covers $4\le n/k\le25$ at these heights, with largest cutoff $972{,}000$. For $n/k\ge96$ the extended radial theorem applies because $0.89\cdot96>47+2.5\cdot15.3$ and $\log n<15.3$.

When $25\le n/k\le96$, use the exterior-root theorem and start the integer middle samples at $\lfloor7\sqrt n/20\rfloor+1$. They lie in $nS^2\ge6/5$, hence $A\ge\sqrt{(6/5)n}/96>11$. At points where $A\ge37$, every relevant row of the adaptive table supplies the old-root comparison. Otherwise $kS^2=A^2/k<37^2\cdot96/n<1/7$, and the new differentiated comparison applies. Their old integer sample signs agree, and both use the true old angular derivative for the next sign. Reciprocity reflects the middle and exterior intervals. The exterior roots and integer sample gaps exhaust the old degree, so all roots are simple and the signs at the old roots alternate. The constant and leading coefficients of the next polynomial give one root on each outside interval, and the old-root gaps give the rest. This proves strict interlacing at the stated uniform cutoff.

[short]: ../effective-uniform.md
[radial]: ../radial-taylor.md
[small]: ../small-threshold-circle.md
