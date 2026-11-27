# Independent statement review

Agent-assisted review by @all_cutoff_blind_review, November 27, 2026. The reviewer inspected the argument and exact source at `55c5434c4d58f1a486ed383d9e640acdf21445b8` without rebuilding.

The numerator uses the original cutoff-log coefficients at $-\exp(-s)$. Its moment index $d=j+1$ runs precisely from $1$ through $k-1$, and the shifted moment carries the required negative sign and factorial. The series-value equality therefore applies to the literal tilt at both poles.

For index $j\ge1$ the wrapper has $p=2j+1\ge3$. The chord from the principal pole at index zero to index $j$ is vertical at the same real height, and both endpoints satisfy the same radius cap. The bound along the segment follows by convexity of the disk. The log change $(28/25)j$ is $(14/25)(p-1)$, and the exponential’s norm uses the real part of the log difference. This comparison requires no complex-log branch choice.

The radial decay uses $(W/r)^2=1+(p^2-1)(\pi/r)^2$, with $(W/r)^2\le51/50$ from $k\ge100$. The bound $1+z\le50/49$ gives $\log(1+z)\ge(49/50)z$. Halving through the square gives exponent $-(49/100)(p^2-1)$, using $n(\pi/r)^2\ge1$. The joint exponent is at most $-(14/5)j$ since $j^2\ge j$. The weighted geometric majorant sums over $j\ge1$ to $1/4$. Division by $p\ge3$ gives $1/12$.

The theorem matches the stated scope. The exported budget covers the finite positive nonprincipal labels with a common normalization. Conjugacy extends the comparison by reflection, and the factor of two from summing both signed halves cancels against the contribution of both principal terms. Application of the separate Fourier contrast estimate remains a step of the overall coefficient argument.
