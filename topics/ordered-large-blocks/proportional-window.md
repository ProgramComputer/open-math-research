# Ordered partitions in a bounded proportional window

For $`j≥2`$, let $`O_{n,j}(t)`$ enumerate ordered set partitions of $`[n]`$ by blocks of size at least $`j`$. This window supplies the bounded-degree case of the [uniform outer-rank theorem](outer-ranks/README.md). The full all-size conjecture at every threshold remains open. [Original statement](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#openProblemsSetPartitions) · [Research issue](https://github.com/ProgramComputer/open-math-research/issues/1)

**Theorem.** For every fixed $`C>0`$, there is $`J(C)`$ such that if $`j\ge J(C)`$ and $`0\le n\le Cj`$, then $`O_{n,j}(t)`$ has only simple real negative zeros. The consecutive pairs within this range strictly interlace. In increasing modulus, the $`i`$th root of the next row precedes the $`i`$th old root, which precedes the next $`(i+1)`$st root whenever it exists. The upper comparison is omitted at the last root when the next row has the same degree.

### Coefficient limit

Set $`S_j(z)=\sum_{s=1}^{j-1}z^s/s!`$ and $`T_j(z)=\sum_{\ell\ge0}j!z^\ell/(j+\ell)!`$. The ordered sequence construction gives

$$
\frac{[t^k]O_{n,j}(t)}{n!}
=\frac{1}{(j!)^k}[z^{n-jk}]\frac{T_j(z)^k}{(1-S_j(z))^{k+1}}.
\tag{1}
$$

The coefficient is zero if $`n<jk`$. On $`|z|\le1`$, $`1-S_j(z)`$ tends uniformly to $`2-e^z`$, and $`T_j(z)`$ tends uniformly to 1. For large $`j`$, Rouché's theorem gives a unique zero $`\rho_j`$ of $`1-S_j`$ inside the unit circle. It is positive and tends to $`\log 2`$, since $`S_j`$ is strictly increasing for positive real $`z`$ and converges uniformly near $`\log 2`$. Set $`\kappa_j=\rho_jS'_j(\rho_j)>0`$.

Define

$$
G_{j,k}(z)=T_j(z)^k\left(\frac{1-z/\rho_j}{1-S_j(z)}\right)^{k+1}.
$$

The apparent singularity at $`\rho_j`$ is removable and $`G_{j,k}(\rho_j)=T_j(\rho_j)^k/\kappa_j^{k+1}`$. For bounded $`k`$, the functions $`G_{j,k}`$ are uniformly bounded on the unit circle because $`1-S_j`$ is bounded away from zero there. Consequently their Taylor coefficients $`g_\ell`$ are uniformly bounded by Cauchy's estimate. For $`m=n-jk\ge0`$ and $`k\ge1`$,

$$
\begin{aligned}
[z^m]\frac{G_{j,k}(z)}{(1-z/\rho_j)^{k+1}}
&=\rho_j^{-m}\sum_{\ell=0}^m g_\ell\rho_j^\ell\binom{m-\ell+k}{k}\\
&=\rho_j^{-m}
 \left(\frac{G_{j,k}(\rho_j)m^k}{k!}
       +O_k((m+1)^{k-1})\right).
\end{aligned}
$$

For the estimate, the binomial coefficient differs from $`m^k/k!`$ by $`O_k((1+\ell)(m+1)^{k-1})`$ when $`0\le\ell\le m`$, and the omitted geometric tail is $`O_k(m^k\rho_j^{m+1})`$. The $`k=0`$ formula has error $`O(\rho_j^{m+1})`$ inside the parentheses and main term $`G_{j,0}(\rho_j)`$. All constants can be taken independent of $`j`$ since $`\rho_j`$ is bounded away from 1.

Use the positive rescaling

$$
Q_{n,j}(x)=\frac{\kappa_j\rho_j^n}{n!}
O_{n,j}\left(\frac{\kappa_j j!}{j\rho_j^jT_j(\rho_j)}x\right).
$$

Equations (1) and the estimate give $`[x^k]Q_{n,j}=((n/j-k)_+)^k/k!+O_C(j^{-1})`$ for each $`1\le k\le C`$, uniformly for $`j\le n\le Cj`$, where $`a_+=\max(a,0)`$. The constant coefficient tends uniformly to 1 on the same range. Thus, whenever $`n/j\to c`$ in this range, $`Q_{n,j}`$ converges coefficientwise to

$$
F_c(x)=1+\sum_{k\ge1}\frac{(c-k)_+^k}{k!}x^k.
\tag{2}
$$

The polynomial $`F_c`$ is the finite-volume grand partition function for classical unit hard rods on a segment of length $`c`$. Its $`k`$th coefficient is the volume of ordered starting positions with gaps at least one. Subtracting the compulsory gaps gives a simplex of side $`c-k`$. Hard-rod zeros and their thermodynamic limit have a separate literature. The argument below gives the finite-volume simplicity and root motion needed for the ordered set partitions. [Ibsen, Cordero and Tabensky, Sections II and V](https://www.cec.uchile.cl/cinetica/pcordero/articles/97_JChemPhys_107.pdf), [Hauge and Hemmer reference and context](https://annals.math.princeton.edu/wp-content/uploads/annals-v158-n3-p07.pdf).

### Simple negative roots of the limit

Let $`G_{L,c}`$ have vertex positions $`1,\ldots,\max(0,\lfloor cL\rfloor-L+1)`$, with two distinct positions adjacent when their distance is less than $`L`$. It is claw-free because the neighbors on either side of any vertex form a clique. For $`c\ge1`$, the number of size-$`k`$ independent sets is $`\binom{\lfloor cL\rfloor-kL+k}{k}`$, taking this count as zero when the top is smaller than $`k`$. To count them, subtract $`(i-1)(L-1)`$ from the $`i`$-th selected position. The resulting positions are strictly increasing, and their maximum allowed position is reduced by $`(k-1)(L-1)`$. Hence the independence polynomial $`I(G_{L,c},x/L)`$ converges to $`F_c(x)`$. Chudnovsky and Seymour's theorem and closure of real-rootedness under coefficientwise limits of bounded degree give real-rootedness of $`F_c`$.

For any $`c-1\le u<c`$ with $`u>1`$, the terminal vertices of $`G_{L,c}`$ omitted in $`G_{L,u}`$ form a simplicial clique. There are at most $`L`$ of them, and for each removed vertex its neighbors outside the clique are all to its left within distance $`L-1`$, so they form a clique. By Chudnovsky and Seymour's Lemma 2.5(1) with the empty clique as its second clique, $`I(G_{L,c},x)`$ is compatible with $`I(G_{L,u},x)`$. By Lemma 2.5(2), it is also compatible with $`xI(G_{L,u},x)`$. Here compatibility means every nonnegative linear combination is real-rooted. Rescaling and taking limits gives compatibility of $`F_c`$ with each of $`F_u`$ and $`xF_u`$. [Chudnovsky and Seymour, Theorem 1.1 and Lemmas 2.5 and 3.4](https://doi.org/10.1016/j.jctb.2006.06.001).

If $`F_c`$ has a repeated root $`a`$, then $`a<0`$ and $`c>2`$. For any such $`u`$, suppose $`F_u(a)\ne0`$. Choose two nearby negative thresholds $`x_-<a<x_+`$ with no $`F_u`$ zero between them. Count roots at or above each threshold with multiplicity. If $`F_u`$ has count $`b`$ at both thresholds, $`xF_u`$ has count $`b+1`$ at both. Lemma 3.4 says compatible polynomials with positive leading coefficients give counts differing by at most one at every threshold. Thus $`F_c`$ has count in $`\{b,b+1\}`$ at both thresholds, contrary to its drop by at least two. Therefore $`F_u(a)=0`$ for all $`c-1<u<c,\ u>1`$. Such $`u`$ contain an open interval between two consecutive integers. On that interval $`F_u(a)`$ is a nonzero polynomial in $`u`$, since its highest included term has leading coefficient $`a^{\lfloor u\rfloor}/\lfloor u\rfloor!`$. This contradiction proves simplicity.

### Strict motion of the limit roots

The same root-count bound gives oriented interlacing for $`c-1\le u<c,\ u>1`$. At any negative threshold the root count of $`F_c`$ is the count of $`F_u`$ or one greater, by applying Lemma 3.4 to both $`F_u`$ and $`xF_u`$. Write $`\lambda_i(c)`$ for the $`i`$th root from the right, defined on $`c>i`$. The count bound gives $`\lambda_i(c)\ge\lambda_i(u)\ge\lambda_{i+1}(c)`$ whenever the indicated roots exist. In particular $`\lambda_i(c)`$ is nondecreasing. All the roots are simple and finite on their respective domains, and the coefficients are continuously differentiable for $`c>1`$, including at integers since the newly appearing term is of order at least two. Thus each $`\lambda_i`$ is continuously differentiable by the implicit function theorem.

For $`c>1`$, (2) yields the delay identity $`\partial_c F_c(x)=xF_{c-1}(x)`$, with $`F_v=1`$ for $`0\le v\le1`$. A zero derivative of $`\lambda_i(c)`$ therefore requires a common negative root of $`F_c`$ and $`F_{c-1}`$. Interlacing allows two equalities. The first is $`\lambda_i(c)=\lambda_i(c-1)`$, which makes the root constant on that interval by monotonicity. This contradicts the same nonzero-polynomial argument used for simplicity. The second is $`\lambda_i(c)=\lambda_{i-1}(c-1)`$. The differentiable function $`\lambda_i(v)-\lambda_{i-1}(v-1)`$ is nonpositive near $`c`$ and attains zero at $`c`$, so the two derivatives coincide there. A zero derivative at $`c`$ would force a zero derivative at $`c-1`$. Iteration lowers the rank until either the second equality is impossible at rank one or $`1<c\le2`$. In the latter range the single root is $`-1/(c-1)`$ and its derivative is positive. Hence every root derivative is strictly positive.

### Uniform real-rootedness and interlacing

For any sequence $`j\to\infty`$ and $`j\le n\le Cj`$, pass to a subsequence with $`n/j\to c`$. The polynomial $`Q_{n,j}`$ has degree $`\lfloor n/j\rfloor`$. Around each simple negative root of $`F_c`$, choose a small disk symmetric about the real axis, disjoint from the other disks. Coefficient convergence and Rouché's theorem give exactly one simple real root of $`Q_{n,j}`$ in that disk, since a nonreal root would have its conjugate there as well. If $`c`$ is nonintegral this accounts for all roots. If $`c`$ is integral, $`F_c`$ has degree $`c-1`$, so there is at most one extra root, which must also be simple and real by conjugacy. It tends to $`-\infty`$ on any subsequence where it exists, because Rouché's theorem on a large fixed circle gives exactly $`c-1`$ roots inside. All roots must be negative by positivity of the coefficients. This proves uniform real-rootedness by compactness.

For interlacing, write $`A_k(n)=[x^k]Q_{n,j}(x)`$ and $`\Delta A_k=A_k(n+1)-A_k(n)`$. The convolution in the coefficient limit gives, for $`k\ge1`$ and $`m=n-jk\ge-1`$,

$$
\Delta A_k=\frac{\kappa_j^{k+1}}{j^k T_j(\rho_j)^k}
\sum_{\ell=0}^{m+1}g_\ell\rho_j^\ell\binom{m-\ell+k}{k-1}.
\tag{3}
$$

This is Pascal's identity, with the $`\ell=m+1`$ term included. For $`k=0`$, the difference is exponentially small for $`n\ge j`$. For bounded $`k`$, all the differences are $`O(j^{-1})`$ when $`j\le n\le Cj`$. Applying the geometric-tail estimate to (3) with $`k-1`$ in place of $`k`$ gives, for $`n/j\to c>1`$,

$$
j\left(Q_{n+1,j}(x)-Q_{n,j}(x)\right)\longrightarrow\partial_c F_c(x)
$$

coefficientwise. For the coefficient where $`m/j\to0`$ and $`k\ge2`$, this also follows from the bound $`O((m+2)^{k-1}/j^k)`$ in (3), which includes $`m=-1`$. If $`m<-1`$, both coefficients are zero.

At a root $`a_j\to\lambda_i(c)`$ of $`Q_{n,j}`$, the quotient

$$
j\frac{Q_{n+1,j}(a_j)}{Q_{n,j}'(a_j)}
\longrightarrow
\frac{\partial_c F_c(\lambda_i(c))}{F_c'(\lambda_i(c))}
=-\lambda_i'(c)<0.
\tag{4}
$$

This proves the required signs at all roots with a finite limit. When $`c=1`$, there are no such roots.

It remains to check an extra root $`a_j\to-\infty`$ when $`n/j\to c=D`$ is integral and $`n\ge Dj`$. Then the two degrees are both $`D`$ for large $`j`$, $`m=n-Dj=o(j)`$, and the equation $`Q_{n,j}(a_j)=0`$ gives

$$
A_D(n)a_j=-A_{D-1}(n)+o(1)\longrightarrow-\frac1{(D-1)!}.
\tag{5}
$$

If $`m\to\infty`$, the same convolution estimates applied to $`A_D`$ and (3) give $`\Delta A_D/A_D(n)\sim D/m`$. This covers $`D=1`$ as well. If $`m`$ stays bounded, pass to a subsequence with $`m`$ fixed. By (1) and the normalization, the ratio $`\Delta A_D/A_D(n)`$ tends to

$$
\frac{b_{m+1}-b_m}{b_m},\qquad b_s=[z^s](2-e^{\rho z})^{-D-1},\qquad \rho=\log 2.
$$

This is positive, as proved below. Both cases imply $`j\Delta A_D/A_D(n)\to+\infty`$. By (5) and the uniform $`O(j^{-1})`$ bound on the other differences,

$$
\frac{Q_{n+1,j}(a_j)}{a_j^{D-1}}
=a_j\Delta A_D+O(j^{-1})<0
$$

eventually. The derivative $`Q_{n,j}'(a_j)`$ has the sign of $`a_j^{D-1}`$ because $`a_j`$ is the leftmost simple root and the leading coefficient is positive. This proves the quotient in (4) is negative at the extra root as well.

To verify the coefficient positivity just used, first take $`D=1`$. The function

$$
H(z)=\frac{1-z}{(2-e^{\rho z})^2}-\frac{1}{4\rho^2(1-z)}
$$

is analytic on $`|z|\le2`$ after removing its apparent pole at $`z=1`$. The other zeros of $`2-e^{\rho z}`$ are $`1+2\pi i k/\rho`$, $`k\ne0`$. On the circle $`|z|=2`$, put $`w=\rho(z-1)=a+ib`$. The identity $`|1-e^w|^2=(1-e^a)^2+2e^a(1-\cos b)`$ gives $`|1-e^w|\ge |w|/8`$: use $`e^a\ge 1/8`$, $`|1-e^a|\ge |a|/8`$, and $`1-\cos b\ge2b^2/\pi^2`$ for $`|b|<\pi`$. Thus $`|H(z)|\le65/(4\rho^2)`$ on that circle. For $`s\ge7`$, the Cauchy bound $`65\cdot 2^{-s}<1`$ shows that the coefficient of $`z^s`$ in $`(1-z)/(2-e^{\rho z})^2`$ is strictly positive. For $`s=0`$ its coefficient is 1. For $`1\le s\le6`$, if $`h_s=[z^s]\,(2-e^z)^{-2}`$, the successive ratios $`h_{s-1}/h_s`$ are $`1/2,1/2,6/11,4/7,385/653,3918/6497`$, all less than $`2/3<\rho`$. This gives $`\rho^s h_s-\rho^{s-1}h_{s-1}>0`$. For $`D>1`$, multiply the positive series by $`(2-e^{\rho z})^{-(D-1)}`$, which has nonnegative coefficients and constant 1. Therefore $`b_{m+1}-b_m>0`$ for all $`m\ge0`$.

For real-rooted polynomials of successive degrees equal or differing by one, negative values of $`Q_{n+1,j}(a)/Q'_{n,j}(a)`$ at every simple root $`a`$ of $`Q_{n,j}`$ give strict directed interlacing. Indeed $`Q_{n+1,j}`$ changes sign between successive roots of $`Q_{n,j}`$ and between its rightmost root and zero. If the degree increases, the sign at $`-\infty`$ forces a further root to the left. A constant first polynomial interlaces any following polynomial of degree at most one, so the pairs with $`n<j`$ are immediate. Every sequence with $`j\to\infty`$ and $`j\le n<n+1\le Cj`$ has a subsequence as above, and the signs eventually hold on it. A sequence of violations is impossible, which proves the stated uniform result.
