# Uniform numerator contraction at small height

Let $k\ge100$, $0\le s\le4\sqrt{k}$, $p=s+i\pi$, $r=|p|$, $S=\pi/r$, and $\rho=1-1/k$. Let $L$ be the analytic logarithm of $(1+e^{w-s})/(1+e^{-s})$ on $|w|<r$, with $L(0)=0$, and let $G$ be its Taylor polynomial through degree $k-1$. For a nonzero $w$ put $\widehat w=\rho r w/|w|$. For every $r\le |w|\le (1+1/k)r$,

$$
 |G(w)-L(\widehat w)|+|G(p)-L(\widehat p)|\le\frac{2997}{100}<30 .
$$

The bound is uniform even when the outer circle intersects another pole. Both log evaluations occur inside the nearest-pole disk. This supplies the small-height comparison in the [wider-circle argument](../../fourier-circle/README.md) and sharpens the budget in the [radial Taylor estimates](../../radial-taylor.md).

## Normalized coefficients

Write $A_j=r^j[w^j]L(w)$. The logistic value and the odd-pole coefficient identity give

$$
 |A_1|=\frac r{1+e^s}\le e^{-s}(s+\pi)\le\pi<4,\qquad
 A_j=-\frac1j\sum_{m\ \mathrm{odd}}\left(\frac r{s+im\pi}\right)^j\quad(j\ge2).
$$

The linear estimate uses $r\le s+\pi$ and $e^s\ge1+s$. The nonlinear identity is for the analytic Taylor series in every degree. In the range $2\le j<k$ it agrees with the original cutoff coefficient.

For $m=\pm(2\ell+1)$, $\ell\ge1$, the absolute summand is $(1+4\ell(\ell+1)S^2)^{-j/2}$. Bernoulli's inequality at exponent $j/2\ge1$ bounds it by $(1+2jS^2\ell^2)^{-1}$. For $B=S\sqrt{2j}$ this function of $\ell$ is decreasing on $[0,\infty)$. Integrating over $[\ell-1,\ell]$ and summing bounds the half-lattice by $\pi/(2B)$. Including the two nearest poles and using $\pi<3.15<9\sqrt2/4$ gives

$$
 j|A_j|\le 2+\frac{9}{4S\sqrt j}.
$$

This establishes absolute convergence of the pole sum and of the Taylor series at each contracted point.

## Radial comparison

Put $u=1/k$ and $a=e-e^{-1}+1/(k-1)$. For $1\le j<k$,

$$
 \frac{(1+u)^j-(1-u)^j}{j}\le\frac a k,\qquad
 \frac{1-(1-u)^j}{j}\le\frac1k.
$$

For the first inequality, $(1+u)^j\le e^{ju}$. Applying $\log x\le x-1$ to $1/(1-u)$ gives $\log(1-u)\ge-u/(1-u)$. With $t=ju$ and $\delta=ju/(k-1)$, this yields $(1-u)^j\ge e^{-t-\delta}\ge e^{-t}-\delta$ using $e^{-\delta}\ge1-\delta$ and $e^{-t}\le1$. Convexity of $e^t-e^{-t}$ on $[0,1]$ bounds it by $(e-e^{-1})t$. The second inequality follows from $(1-u)^j\ge1-ju$. The rational bound $e<68/25$ gives $a\le68/25-25/68+1/99<19/8$.

Set $U=1/(S\sqrt k)$. Using the radius-difference inequalities on the two rays, the absolute cost of the degrees $2$ through $k-1$ is at most $(19/8)(2+9U/2)$ for $w$ and $2+9U/2$ for $p$. Indeed

$$
 \sum_{j=2}^{k-1}\frac1{\sqrt j}\le
 \sum_{j=2}^{k-1}2(\sqrt j-\sqrt{j-1})\le2\sqrt k .
$$

The first-degree costs together are at most $12/k$. At radius $\rho r$, the omitted series on each ray costs at most

$$
 \sum_{j\ge k}\frac{2+9U/4}{k}e^{-j/k}
 =\frac{2+9U/4}{e\,k(1-e^{-1/k})}
 \le \frac38(2+9U/4).
$$

Here $e^{1/k}\ge1+1/k$ implies $k(1-e^{-1/k})\ge k/(k+1)\ge100/101$, and $e>2.718$ gives $101/(100e)<3/8$. The height assumption gives $U^2=s^2/(\pi^2 k)+1/k\le16/\pi^2+1/100<(32/25)^2$ since $\pi>3.14$. Combining the contributions gives

$$
 \frac{12}{100}+\left(\frac{19}{8}+1\right)
 \left(2+\frac92\frac{32}{25}\right)
 +2\frac38\left(2+\frac94\frac{32}{25}\right)
 =\frac{2997}{100}.
$$

## Formal scope

[NumeratorLogSeries.lean](NumeratorLogSeries.lean) proves the two-ray bound for the explicit odd-pole series in normalized coordinates. Its zeroth coefficient is zero, its first is $r/(1+e^s)$, and its higher coefficients use all signed odd poles. It proves the stated rational bound without hypotheses on the coefficients. The Lean theorem compares the finite sum through degree $k-1$ with the infinite sum at each contracted point. The analytic identification with $L$ is a separate step in the displayed mathematical argument.

The support is in [NumeratorPoleVolume.lean](NumeratorPoleVolume.lean), [NumeratorOddPoleMoment.lean](NumeratorOddPoleMoment.lean), [NumeratorRadialScalars.lean](NumeratorRadialScalars.lean), and [NumeratorTaylorContraction.lean](NumeratorTaylorContraction.lean).

The pinned [Fourier workflow](../../../../.github/workflows/long-cycle-fourier-contrast.yml) runs the [checker](check.py) from the repository root with:

    cd shared/lean
    lake env python3 -I ../../topics/long-cycle-excedances/lean/fourier-circle/check.py

The workflow lists the exact cache modules and checks the axiom reports.

The [verification record](numerator-small-height-verification.md) gives the exact hosted commit, hashes and axiom results.
