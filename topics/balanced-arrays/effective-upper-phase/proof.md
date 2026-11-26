# Effective signs of the leading angular contributions at the last two nodes

Fix integers $`d\ge 10^{12}`$, $`n\ge64d`$ and $`1\le r<d`$. Write $`T=nr/d`$, $`D=\lfloor T\rfloor`$ and $`\nu=(d-1)/2`$. At each $`k=D-1,D-2`$ there is a positive tilt $`v`$ at which the phase of the principal Gaussian term is $`k\pi`$, and the real part of the *sum of all Gaussian angular terms* has strict sign $`(-1)^k`$. The constants are explicit and uniform in the cap. To deduce the sign of the actual balanced-array polynomial requires a separate bound on the transverse integration error. This note only proves the leading-term assertion.

Let the deficit $`J=r-S`$ have weights $`\binom d{r-j}v^{-j}`$, $`0\le j\le r`$. For the second law multiply these weights by $`(r-j)(d-r+j)`$. Denote their probabilities by $`p_j,\tilde p_j`$, their means by $`h,\tilde h`$, and their characteristic functions at $`-t`$ by $`F(t),G(t)`$. Use continuous arguments starting at zero. Define

$$
A(t)=|F(t)|^{n+\nu}|G(t)|^{-\nu},\qquad
\Theta(t)=nr t+(n+\nu)\arg F(t)-\nu\arg G(t).
$$

The leading Gaussian contribution at $`t`$ is a common positive factor (independent of $`t`$) times $`A(t)e^{i\Theta(t)}`$. This follows because the complex transverse variance equals its positive real-tilt value times $`G/F`$. The angles summed are $`t=\ell\pi/d`$, one for each of the $`d`$ odd residue classes modulo $`2d`$, using representatives in $`(-d,d]`$. The assigned arguments agree with the Gaussian square-root branch because $`F,G`$ both stay near one throughout the angular interval below; in particular $`G/F`$ has positive real part. Indeed the zero-atom bounds below give $`|F(t)-1|,|G(t)-1|\le 2(1-(15/16)^2)=31/128`$ for every real $`t`$. Hence $`|F(t)|\ge97/128`$ and $`|G(t)/F(t)-1|\le62/97<1`$. The argument difference is the continuous branch in the right half-plane starting at zero.

Set $`x=r/[(d-r+1)v]`$. The successive deficit weight ratios are at most $`x`$ and the first equals $`x`$. For $`0<x\le x_0=4d/n\le1/16`$ the first law has $`p_0\ge1-x`$, $`p_1=x p_0`$. The ratio of the second law's additional factor at $`j`$ to its value at zero is at most $`j+1`$. Thus both normalized laws have their $`j`$th mass at most $`(j+1)x^j`$ and $`\tilde p_0\ge(1-x)^2`$. Their first, second, and third raw moments are at most $`3x,4x,5x`$, respectively. For example the coefficientwise positive series $`\sum_{j\ge1}j^a(j+1)x^{j-1}`$ is maximized at $`1/16`$ for $`a=1,2,3`$; differentiate the geometric series to verify these three bounds. The first law's sharper bound is $`h\le x/(1-x)^2`$. Both centered third absolute moments are at most $`5x+(3x)^3\le6x`$ by $`|J-h|^3\le J^3+h^3`$.

At $`|t|\le1`$ the centered characteristic function under either law has real part at least $`1-2xt^2\ge7/8`$ and imaginary part of absolute value at most $`x|t|^3`$. This follows by the real Taylor bounds for cosine and sine. Thus

$$
|\Theta(t)-[nr-(n+\nu)h+\nu\tilde h]t|
\le 2(n+2\nu)x|t|^3 .
$$

If $`x\le x_0`$, the right side is at most $`9d|t|^3`$. At $`x=x_0`$, $`h\ge(1-x)x`$ and $`\tilde h\le3x`$, so

$$
((n+\nu)h-\nu\tilde h)/d\ \ge\ (15n/16-3d/2)x_0/d>3.65.
$$

At $`t_*=\pi/d`$ the phase error divided by $`\pi`$ is at most $`9\pi^2/d^2`$. Hence $`\Theta(t_*)/\pi<T-3`$ at $`x_0`$ and tends to $`T`$ at $`x=0`$. By continuity, both stated levels are attained in this interval. At any such level $`T-k\ge1`$. The upper bound $`h\le x/(1-x)^2`$, together with the error bound $`2(n+2\nu)x\pi^2/d^3`$, gives $`T-k\le(5/4)nx/d`$ for $`d\ge16`$. In particular $`nx\ge4d/5`$.

For odd $`|\ell|\le d^{2/3}/8`$, the angular phase differs from $`\ell k\pi`$ by at most

$$
9d(\pi/d)^3(|\ell|^3+|\ell|)\le18\pi^3/512<\pi/2 .
$$

Indeed the linear parts cancel on subtracting $`\ell\Theta(t_*)`$. All these leading terms have positive signed real part, including the principal term with exact magnitude $`A(t_*)`$.

Here are bounds for the discarded leading terms throughout $`|t|\le\pi`$. For the first law, $`1-|F|^2\ge2p_0p_1(1-\cos t)`$, giving $`\log|F|\le-(15/16)^2 x(1-\cos t)`$. For either law, $`1-|F|^2`$ or $`1-|G|^2`$ is at most $`8x(1-\cos t)`$ because $`1-\cos(jt)\le j^2(1-\cos t)`$ and the second moment of the difference of two independent copies equals twice the variance. The moduli are both at least $`2(15/16)^2-1>3/4`$. Therefore their negative logs are at most $`8x(1-\cos t)`$, by $`-\log y\le(1-y^2)/(2y^2)`$. Since $`n\ge64d`$, it follows that

$$
A(t)\le \exp[-(3/4)nx(1-\cos t)],\qquad
A(t_*)\ge \exp[-20\pi^2/d]>1/2 .
$$

The lower bound uses $`nx\le4d`$ and $`1-\cos t_*\le t_*^2/2`$. Using $`1-\cos t\ge 2t^2/\pi^2`$ for $`|t|\le\pi`$, the sum of the magnitudes of all discarded terms is at most

$$
d\exp[-3d^{1/3}/160]<1/2.
$$

Indeed for $`d=10^{12}`$ the exponent is $`187.5`$, and $`\log(2d)/d^{1/3}`$ decreases thereafter. Thus even one principal term outweighs the entire discarded sum, proving the claim. The small rational-tilt experiments in the companion script certify phase alignment only; they do not use the very large bound on $`d`$ or assert a bound on the full chart error.

## Exact finite phase probes

The finite probes start at a positive occupied tilt $`v_0`$. For any $`v\ge v_0`$ the deficit distribution is obtained by reweighting the lower-tilt distribution by $`(v_0/v)^j`$, a nonincreasing function of $`j`$. The covariance-weighted law has the same reweighting on its fixed support. Thus both are stochastically decreasing in $`v`$, by likelihood ratio order, and each raw positive moment at $`v_0`$ bounds the corresponding moment for every later tilt. Centering at the moving mean therefore gives, on any angle with $`1-m_2t^2/2>0`$, a bound $`(m_3+m_1^3)|t|^3/[6(1-m_2t^2/2)]`$ for the argument after removing its linear mean term, where $`m_j`$ are raw moments at $`v_0`$.

The script uses $`\pi<22/7`$ to replace $`|t|`$ by a rational upper angle. At a certified lower tilt the upper bound on $`\Theta(\pi/d)/\pi`$ is less than the target $`k`$, while its limit is $`T>k`$, so a crossing exists at a later tilt. For each reported positive odd label, the sum of its centered phase error and the label times the principal error is less than $`3/2<\pi/2`$ (the principal phase itself is exact at the crossing). For the branch, subtract the arguments of the two characteristic functions. The absolute value of their linear difference is bounded by the larger lower-tilt mean times the rational upper angle, since both current means are nonnegative and bounded by their own lower-tilt means. Add both centered errors. The script checks that this rational bound is below $`3/4<\pi/2`$ for every reported label, including the principal label, uniformly from $`v_0`$ onwards. This verifies the continued Gaussian branch on the retained labels. Negative labels follow by conjugation.

The bracket search selects candidate witnesses. A failure of its sufficient inequality does not rule out a crossing, and stopping the scan of odd labels makes no claim about excluded labels. The search ledger records each actual evaluation, including failed candidates and the archive selections. The finite probes do not bound the discarded angular terms or the full integral.
