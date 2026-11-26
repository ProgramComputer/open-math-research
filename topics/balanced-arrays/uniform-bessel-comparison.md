# Uniform Bessel comparison for singleton slices

Let $T_s(q)$ be the quota series before labeled-row injection for a uniform-weight four-column cap-two array with exactly $2s$ singletons. Use the notation from [the fixed-count and four-singleton note](four-singletons.md). Put $h=\lceil s/2\rceil$ and $U_s(q)=q^{-h}T_s(q)$. The bound $4k\ge2s$ forces at least quota $h$. The singleton distributions $(h,h,h,h)$ for $s=2h$ and $(h,h,h-1,h-1)$ for $s=2h-1$ realize this minimum, respectively using zero or one edge. Thus $U_s(0)>0$. The labeled row multiplier for coefficient $j$ of the reduced slice is $(N)_{2j}$ with $N=n-(2h+s)$, up to the common positive factor $(n)_{2h+s}$ when $n\ge2h+s$.

## A uniform differential-operator factorization

Assign the four colors the Fourier characters
$$
\xi_1=e^{i(\theta_1+\theta_2+\theta_3)},\quad
\xi_2=e^{i(\theta_1-\theta_2-\theta_3)},\quad
\xi_3=e^{i(-\theta_1+\theta_2-\theta_3)},\quad
\xi_4=e^{i(-\theta_1-\theta_2+\theta_3)} .
$$
A monomial in the $\xi_i$ has constant Fourier coefficient exactly when its exponents agree. The two-color character sum is $2\sum_{j=1}^3\cos2\theta_j$, and the singleton character sum is
$$
4\bigl(\cos\theta_1\cos\theta_2\cos\theta_3-i\sin\theta_1\sin\theta_2\sin\theta_3\bigr).
$$
For $q=-z^2$ assign each edge the weight $iz$ before taking the constant term, and multiply the $2s$-singleton slice by $(iz)^s$. A term with $E$ edges and $2s$ singletons has quota $k=(E+s)/2$ when balanced, giving weight $(iz)^{E+s}=q^k$.

For independent variables $z_i$, put $X_i=\partial_{z_i}/(2i)$, $\mathcal A=\prod_i(1+X_i)$, and $\mathcal B=\prod_i(1-X_i)$. Expand the power of the singleton character sum and integrate against the edge exponential. All odd sine exponents integrate to zero. In the even terms use $\cos^2\theta_i=(1+\cos2\theta_i)/2$ and the analogous sine identity. This gives the uniform formula
$$
T_s(-z^2)=\frac{(2iz)^s}{(2s)!}
\left[P_s(\mathcal A,\mathcal B)\prod_{i=1}^3 J_0(2z_i)\right]_{z_i=z},
\qquad
P_s(A,B)=\sum_{j=0}^s(-1)^j\binom{2s}{2j}A^{s-j}B^j .
$$
For $s\ge1$,
$$
P_s(A,B)=\prod_{\ell=1}^s\left(A-\cot^2\!\left(\frac{(2\ell-1)\pi}{4s}\right)B\right).
$$
Indeed $P_s(1,x)=\mathrm{Re}(1+i\sqrt{x})^{2s}$ for $x\ge0$. Its $s$ positive zeros are the squares of the corresponding tangents. The cotangent squares occur in reciprocal pairs, with an extra one for odd $s$.

The operator needs properties of the Bessel input. For $s=2$, its action on the real-stable product $z_1z_2z_3$, restricted to the diagonal, is $(z-i)^3-6z^3+(z+i)^3=-4z^3-6z$, which has nonreal zeros.

## A uniform comparison for the zero count

Write $A(z)=J_0(2z)$, $B(z)=J_1(2z)$ and $W_s(z)=z^{2h-s}U_s(-z^2)$. The fixed-count formula gives the exact identity
$$
W_s(z)=\sum_{\mathbf s:\ \sum_i s_i=2s}
\frac{(-1)^{k_0-h}}{\prod_i s_i!}\prod_{ij\mid kl}J_{|\delta_{ij}|}(2z).
$$
Its parity is that of $s$. For $s\ge1$, put $\kappa_s=4^{2s}/[4(2s)!]$ and take the comparator
$$
L_s(z)=
\begin{cases}
A(z)\bigl(A(z)^2-3B(z)^2\bigr),&s\text{ even},\\
B(z)\bigl(3A(z)^2-B(z)^2\bigr),&s\text{ odd}.
\end{cases}
$$
As $|z|\to\infty$ in the closed right half-plane,
$$
W_s(z)=\kappa_s L_s(z)+O_s\left(|z|^{-5/2}e^{6|\mathrm{Im}\,z|}\right).
$$

To check the leading term, put $\phi=2z-\pi/4$. For fixed integer $d$, the leading term of $\sqrt{\pi z}J_d(2z)$ is $\cos(\phi-d\pi/2)$, with uniform error $O_d(e^{2|\mathrm{Im}\,z|}/|z|)$ on this sector. If $o$ is the number of odd $\delta$'s, the combined sign from the three leading cosines and the coefficient is $(-1)^{k_0-h+(D-o)/2}$. For even $s$, the two possibilities $o=0,2$ give $+\cos^3\phi$ and $-\cos\phi\sin^2\phi$. For odd $s$, $o=1,3$ give $+\cos^2\phi\sin\phi$ and $-\sin^3\phi$. The weights of the four admissible parity triples are equal. To see this, assign $2s$ independent uniform colors and consider $(-1)^{\delta_{12}},(-1)^{\delta_{13}},(-1)^{\delta_{14}}$. Their product is fixed. Each of the three nontrivial characters on the four-element parity set has mean zero because the one-draw mean of the corresponding two-color parity sign is zero. The leading trigonometric polynomial for $W_s$ is therefore $\kappa_s\cos3\phi$ or $\kappa_s\sin3\phi$ after the common factor $(\pi z)^{-3/2}$ is removed. The comparator has the same leading term with $\kappa_s$ removed. [Uniform Bessel asymptotics, DLMF 10.17.3](https://dlmf.nist.gov/10.17.E3)

For odd $s$ choose circles centered at zero with radii the sufficiently large positive zeros of $A$. At the positive real radius, $|\sin3\phi|$ is bounded below because $\cos\phi=O(1/|z|)$ there. For even $s$ use the positive zeros of $B$ and the corresponding lower bound for $|\cos3\phi|$. On the right semicircle the trigonometric lower bound is a constant times $e^{6|\mathrm{Im}\,z|}$. When $|\mathrm{Im}\,z|\le1$, the real part differs from the positive radius by $O(1/|z|)$. When $|\mathrm{Im}\,z|>1$, the hyperbolic-sine part of the modulus gives the bound. Parity handles the left semicircle. Thus for large comparison radii the asymptotic error is smaller than $\kappa_s|L_s|$ on the entire circle. Rouché gives the same zero counts for $W_s$ and $L_s$.

The comparator zeros are all real. The ratio
$$
\frac{B(z)}{A(z)}
=z\sum_{\ell\ge1}\frac{1}{a_\ell-z^2}
=\frac12\sum_{\ell\ge1}\left(\frac{1}{\sqrt{a_\ell}-z}
-\frac{1}{\sqrt{a_\ell}+z}\right)
$$
has positive imaginary part in the upper half-plane, and is strictly increasing on each real gap between its poles. The paired partial-fraction series converges, and its summands have positive imaginary parts termwise. The zeros of $A$ are simple and $A'=-2B$, so there are no common zeros. This proves that the comparator's zeros are real and simple.

Moreover, disjoint disks of a small fixed radius centered at the large positive zeros of the leading $\cos3\phi$ or $\sin3\phi$ each contain one zero of both functions, by the uniform asymptotics and Rouché. Choose the radius smaller than a quarter of the leading zero spacing. The zero of $W_s$ in each disk is real by conjugation, and parity gives the negative ones. The large comparison circles stay a positive distance from the leading trigonometric zeros, so these disks lie wholly inside or outside each such circle. The equal total counts on the large circles then show that every fixed $s$ has only finitely many nonreal zeros. A real sign count in the finite initial part suffices to establish real-rootedness.

## Applying the comparison to six singletons

Write $F^{(3)}=K$, with $F,G,H$ from the previous note. For $s=3$, $h=2$, the reduced series is
$$
U_3(q)=\tfrac32GF^2+q\left(\tfrac16KF^2+2HGF+\tfrac76G^3\right)
+q^2\left(\tfrac14KG^2+\tfrac12H^2G\right)
+\tfrac1{10}q^3KH^2+\tfrac1{180}q^4K^3 .
$$
The contributions before removing the common factor $q^2$ are as follows.

| Singleton counts | Contribution |
| --- | --- |
| $6,0,0,0$ | $q^6K^3/180$ |
| $5,1,0,0$ | $q^5KH^2/10$ |
| $4,2,0,0$ | $q^4KG^2/4$ |
| $4,1,1,0$ | $q^4H^2G/2$ |
| $3,3,0,0$ | $q^3KF^2/6$ |
| $3,2,1,0$ | $2q^3HGF$ |
| $3,1,1,1$ | $2q^3G^3/3$ |
| $2,2,2,0$ | $q^3G^3/2$ |
| $2,2,1,1$ | $3q^2GF^2/2$ |

For positive $u$ off the poles put $R=G(-u)/F(-u)$. The normalized derivative ratios of orders zero through three at $-u$ are $1$, $R$, $(R-1)/u$, and $(2(R-1)-uR)/u^2$. Consequently
$$
45u^2U_3(-u)/F(-u)^3=P(u,R),
$$
where
$$
\begin{aligned}
P(u,R)={}&(24u-2)+(6-45u+192u^2)R\\
&+(-6+33u-168u^2)R^2+(2-12u+51u^2-64u^3)R^3.
\end{aligned}
$$
The first positive zero $a_1$ of $F(-u)$ is greater than one. On $[0,1]$ group the alternating series after its first two terms in pairs. The pair $u^2/4-u^3/36$ is positive for $u>0$, so the series is positive there. For $u\ge1$, the cubic coefficient of $P(u,R)$ is at most $2-12u-13u^2<0$. Also $P(u,0)>0$, whereas
$$
P\!\left(u,-\frac1{\sqrt u}\right)
=-128u^{3/2}-144u-6\sqrt u+31+\frac6{\sqrt u}-\frac6u-\frac2{u^{3/2}}<0.
$$

In every gap $(a_j,a_{j+1})$, the ratio $\sqrt u R$ increases continuously from $-\infty$ to $+\infty$. The sign of $P$ in order is positive near the left pole, negative at $\sqrt uR=-1$, positive at $R=0$, and negative near the right pole. There are at least three real zeros in each gap. There is at least one before the first pole. In fact $U_3(0)>0$, and clearing denominators gives $45a_1^2U_3(-a_1)=p_3(a_1)G(-a_1)^3<0$, where $p_3$ is the cubic coefficient and $G(-a_1)>0$ by the first simple downward crossing of $F(-u)$.

The odd comparator $B(3A^2-B^2)$ has the roots at $B/A\in\{-\sqrt3,0,\sqrt3\}$ and a simple zero at zero. It has one positive zero before the first positive zero of $A$ and three between every successive pair of positive zeros of $A$. Thus the found real zeros of $zU_3(-z^2)$ already exhaust its Rouché count on each sufficiently large comparison circle, together with the zero at zero and the reflections. All zeros of $U_3(-u)$ are positive real. The order and canonical-product argument in the [four-singleton note](four-singletons.md) gives strict interlacing of the nonzero slice roots. The counting problem for arbitrary $s$ remains open.
