# Algebraic checks for strict ordering of the angular phase

Put $`\theta=\pi/d`$, $`z=w e^{i\theta}`$, $`w>0`$, and let $`H`$ and $`B`$ be the truncated binomial polynomials with parameters $`(d,r)`$ and $`(d-2,r-1)`$. For $`1\le r<d`$, all terms of each polynomial lie in an angular sector of width less than $`\pi`$, so each sum is nonzero. Write $`D=w\,\mathrm d/\mathrm dw`$. For a real-coefficient polynomial $`F(z)=\sum_i f_i z^i`$ put

$$
L_F=|F(z)|^2,\qquad
K_F=\Im\bigl(zF'(z)\overline{F(z)}\bigr)
=\sum_{i>j}(i-j)\sin((i-j)\theta)f_if_j w^{i+j}.
$$

Then $`D\arg F=K_F/L_F`$. In particular $`D\arg H>0`$. It suffices to check $`n=d`$, where the phase derivative multiplied by the strictly positive $`2L_HL_B`$ is $`(3d-1)K_H L_B-(d-1)K_B L_H`$.

## Exact finite certificate through dimension 128

The stronger expression $`2K_HL_B-K_BL_H`$ has strictly positive coefficients at every degree $`1,\ldots,4r-3`$ for $`2\le d\le128`$ and $`1\le r<d`$, as checked by [verify-phase-order.py](verify-phase-order.py). The degrees $`0`$ and $`4r-2`$ vanish for structural reasons. This proves $`D\arg B<2D\arg H`$ throughout that finite dimension range and gives strict phase ordering for every $`n\ge d`$ there.

Run from this directory with standard Python 3.

~~~sh
python3 -B verify-phase-order.py
~~~

The run checked 8,128 cap-dimension pairs, 1,373,632 strictly positive interior coefficients, and 16,256 structural endpoint zeros.

The certificate evaluates all trigonometric quantities by enclosing integer intervals of scale $`2^{192}`$. It first encloses $`\pi`$ by Machin's identity $`16\arctan(1/5)-4\arctan(1/239)`$ with two successive alternating sums for each arctangent. The tangent identity follows from $`\tan(4\arctan(1/5))=120/119`$ and $`\tan(4\arctan(1/5)-\arctan(1/239))=1`$. The angle in the last tangent lies in $`(0,\pi/2)`$. The sine and cosine Taylor terms use integer outward rounding on $`[0,\pi/2]`$, the alternating tail bound, and the Lipschitz constant one to turn enclosure of a rounded argument into enclosure at $`j\pi/d`$. Reflection gives the other gaps. The midpoint of an even dimension is an exact integer interval.

The checker forms bounds on $`K_F`$ from the sine formula above and on $`L_F`$ from the cosine counterpart

$$
L_F=\sum_i f_i^2 w^{2i}+2\sum_{i>j}\cos((i-j)\theta) f_i f_j w^{i+j}.
$$

It checks nonnegativity of the four interval arrays used for the products and takes the lower coefficient bound $`2K_H^{\mathrm{lo}} L_B^{\mathrm{lo}}-K_B^{\mathrm{hi}} L_H^{\mathrm{hi}}`$ at squared scale. These convolutions pack the nonnegative arrays as radix digits with a width calculated from both maxima and the maximum number of summands, so no carry can mix neighboring coefficients. Results are strict integer inequalities at all interior positions. The script has no numerical library dependency and writes no data files.

For context, nonnegativity of the exact coefficients of $`L_H,L_B`$ also has a direct argument. For $`F=F_{m,r}(z)=\sum_{i\le r}\binom mi z^i`$ fix a total $`i+j=k`$. In the full binomial pair, the coefficient divided by the positive count is the average cosine of the gap. Truncating both indices to $`i,j\le r`$ intersects the pair range with a symmetric central interval, retaining only smaller absolute gaps. Cosine decreases over the available gap angles in $`[0,\pi]`$, so the conditional average can only increase. The full coefficient is nonnegative from $`(1+2w\cos\theta+w^2)^m`$.

## An exact obstruction to factor one

At the last nonzero degree $`4r-3`$ for $`r\ge2`$, the ratio of the coefficients of $`K_BL_H`$ and $`K_HL_B`$ is exactly

$$
\frac{\binom{d-2}{r-2}/\binom{d-2}{r-1}}
     {\binom d{r-1}/\binom d r}
=\frac{(r-1)(d-r+1)}{r(d-r)}.
$$

The same ratio is the limit of $`(D\arg B)/(D\arg H)`$ as $`w\to\infty`$. For $`d=4,r=3`$ the cleared coefficient of $`K_HL_B-K_BL_H`$ is $`-8\sin(\pi/4)`$ at degree $`9`$, and the derivative ratio tends to $`4/3`$. Thus there are finite tilts at which factor one fails. As $`r=d-1`$ and $`d`$ grows the ratio tends to two, so a universal factor strictly smaller than two is impossible. This does not obstruct the phase derivative with its actual larger coefficient ratio.

## Two all-dimension cases

For $`r=1`$, $`B=1`$ and strictness follows from $`K_H>0`$. For $`r=2`$ put $`p=d(d-1)/2`$, $`b=d-2`$, $`c=\cos\theta`$ and $`s=\sin\theta`$. Expansion of $`(2K_HL_B-K_BL_H)/s`$ gives the following coefficients at degrees $`1`$ through $`5`$:

$$
\begin{aligned}
&2d-b,\\
&2dbc+8pc,\\
&bd(d-4)+12pb c^2+2p(d+b),\\
&8p c b^2+2d pbc,\\
&pb(2db-p).
\end{aligned}
$$

They are positive for $`d\ge3`$. For the third term at $`d=3`$ the first summand is $`-3`$ and the final one is $`24`$. The final line has $`2db-p=d(3d-7)/2>0`$. This gives a direct coefficient proof of the factor-two claim for these caps in every dimension.

For $`r=d-1`$, the factor-two inequality also follows pointwise in every dimension. The only remaining dimensions for this argument are $`d\ge4`$, since $`d=2,3`$ were handled above. Write $`C=1+z`$, $`\eta=\arg C\in(0,\theta)`$, $`p=z/C`$, $`\beta=\Im p>0`$, and $`R=(\sin\eta/\sin\theta)^d`$. Then $`B=C^{d-2}`$, $`H=C^d-z^d`$, and $`p^d=-R e^{-id\eta}`$. The last identity uses $`w/|C|=\sin\eta/\sin\theta`$. Since $`D\log H=d(p-p^d)/(1-p^d)`$, we get

$$
\frac{D\arg H}{d\beta}
=\frac{1-R\thinspace{}\sin((d-1)\eta)/\sin\eta}{1+2R\cos(d\eta)+R^2}.
$$

To show $`2D\arg H\ge D\arg B=(d-2)\beta`$, put $`y=d(\theta-\eta)`$, $`a=-\log R`$, and $`c=\cot\eta`$. Clearing the positive denominator reduces the inequality to

$$
F(y):=\sinh a+\frac2d(\cosh a-\cos y)-c\sin y\ge0.
$$

Here $`a'=c`$ and $`c'=(1+c^2)/d`$ with respect to $`y`$, so

$$
F'(y)=c(\cosh a-\cos y)+\frac{2c}{d}\sinh a+\frac{1-c^2}{d}\sin y.
$$

In fact $`2\sinh a\ge c\sin y`$ on the whole interval. If $`\eta\le\theta/2`$, then $`e^{a}\ge(2\cos(\theta/2))^d>(9/5)^d`$, hence $`2\sinh a>d`$. Also $`c\sin y=\cot\eta\sin(d\eta)\le d\cos\eta\le d`$, by the bound $`|\sin(d\eta)|\le d|\sin\eta|`$. If $`\eta\ge\theta/2`$, convexity of cotangent gives $`a\ge y\cot((\eta+\theta)/2)`$. Put $`m=(\eta+\theta)/2`$. The ratio $`\cot m/\cot\eta`$ is at least $`(\cos\theta/\cos(\theta/2))(\eta/m)>(3/4)(2/3)=1/2`$. Here $`\sin x/x`$ is decreasing, and for $`\theta\le\pi/4`$ the ratio $`\cos\theta/\cos(\theta/2)`$ decreases to a value above $`3/4`$. Thus $`2\sinh a\ge2a\ge cy\ge c\sin y`$ in this case as well. Substitution gives $`F'(y)\ge c(\cosh a-\cos y)+\sin y/d>0`$ for $`0<y<\pi`$. Since $`F(0)=0`$, the inequality holds strictly.

## Status of the general coefficient argument

There is no all-dimension proof of the stronger coefficient statement in this note. The cutoff of the exact certificate is independent of any large-dimension estimate. The exact factor-one obstruction explains why treating the weighted row polynomial as always having the smaller angular derivative would fail.
