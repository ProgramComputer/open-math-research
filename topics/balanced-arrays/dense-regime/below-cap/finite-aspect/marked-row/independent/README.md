# Independent exact replay of the million-row sign extension

Agent-assisted verification, 2026-11-26. This replay covers the geometric indices 504159 through 505661 for height $`n=10^6`$, dimension $`d=250000`$ and row cap $`r=127000`$. It checks the stated scalar bounds and sign inequalities. The mathematical transfer from those inequalities to the original array coefficients uses the marked-row loss bounds and the verified geometric-circle sign theorem.

## Reproduction

Run from this directory. The first command needs Python 3 and the adjacent witness CSV. It is the compact, portable replay. The optional C++ generator uses checked 128-bit integer arithmetic and reconstructs a witness for every individual index without an input archive.

~~~sh
python3 -IB verify.py
clang++ -O3 -std=c++17 -Wall -Wextra independent.cpp -o independent
./independent > independent.csv 2> independent-summary.txt
~~~

[Portable checker](verify.py) · [Tilt witnesses](tilt-witnesses.csv) · [Portable output](verify-output.txt) · [Independent generator](independent.cpp) · [Generator summary](independent-summary.txt)

## Directed scalar bounds

Let $`q_r(z)`$ be the mass at $`r`$ in a $`\mathrm{Bin}(d,z)`$ law conditioned to be at most $`r`$. Relative weights start at one at the cap and are propagated downward by the exact ratio $`j(1-z)/[(d-j+1)z]`$. For $`z`$ with denominator $`2^{44}`$, the code rounds relative weights in both directions in units of $`2^{-48}`$. Once the scaled upper weight is at most $`2^{16}`$ and the next ratio is below one, the upper sum includes an exact geometric bound for the rest. The lower sum omits it. The ratios decrease going down, so this tail bound is valid. Reciprocal sums give bounds for $`q_r(z)`$ in units of $`2^{-56}`$.

The lower loss uses five steps from the trivial lower bound zero at height $`n-5`$ and quota $`k-5`$. At each step with current density $`p=k/n`$, the test parameter is rounded down from $`p/[1-(1-p)e_{\mathrm{lo}}]`$. The new lower loss is the lower cap atom times $`\alpha=(1-r/d)/(1-p)`$, rounded down. For the upper loss each listed tilt is a witness, with no assumption that it solves the mean equation. The checker verifies

$$
d(z-k/n)\ge z(d-r)q_r(z)
$$

using an upper enclosure on the right. The truncated mean is then at least $`dk/n`$. Monotonicity of the mean and cap atom allows this atom times $`\alpha`$, rounded up, as an upper loss.

## Tests and endpoints

For a block of geometric indices $`a,\ldots,b`$, use the lower loss at $`a-2`$ and the upper loss at $`b+2`$. The first 229 blocks cover all 1,452 positions from 504159 through 505610 without gaps. They pass the exact test $`4d(e_{\mathrm{hi}}-e_{\mathrm{lo}})<1-e_{\mathrm{hi}}`$. The minimum integer margin divided by $`2^{56}`$ is $`36824208291462/72057594037927936`$.

For each of the next 51 positions, through 505661, use the exact signed seven-term lower bound

$$
1-2b_1+2\sqrt{b_2b_{-2}}
 \left(\frac{1-e_{\mathrm{hi}}}{1-e_{\mathrm{lo}}}\right)^{d/2}
 -b_3-b_{-3},
$$

where $`b_j`$ are unrestricted term magnitudes divided by the central term at the unrestricted geometric radius. The capped comparison uses the span $`d\log[(1-e_{\mathrm{lo}})/(1-e_{\mathrm{hi}})]`$ of the neighboring log decrements. This is why the attenuation in the even pair is exactly the displayed power. To reconstruct the $`b_j`$ in integer arithmetic, for $`j>0`$ set

$$
B_j(k)=\prod_{i=1}^j
 \frac{(n-k-i+1)^2 k(k+1)}{(k+i)^2(n-k)(n-k+1)}.
$$

Then $`b_j=B_j(k)^{d/2}`$, $`b_{-j}=B_j(n-k)^{d/2}`$ and $`\sqrt{b_2b_{-2}}=[B_2(k)B_2(n-k)]^{d/4}`$. The two exponents are integers. Fixed-point binary exponentiation rounds every multiplication outward. Negative terms use upper bounds and the positive even term uses a lower bound. The minimum signed margin is $`5604823047/281474976710656`$.

The direct generator reproduces the same lower bound at the last positive point. At 505662 the signed lower bound is nonpositive, which only ends this certificate. Combined with the earlier inner interval through 504158 and 95 already certified outer roots, the replay extends the number of isolated simple negative roots to 505756 of degree 508000. The remaining annulus accounts for 2244 roots.
