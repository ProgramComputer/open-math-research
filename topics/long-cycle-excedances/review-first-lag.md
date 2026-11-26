# Review of the first pair with two cycles

This agent-assisted review checks the strict interlacing of rows $2k-1$ and $2k$ for every $k\ge3$. It covers one infinite family of consecutive pairs in Alexandersson’s conjecture. Its independence is limited to the check of this partial theorem. The reviewer has worked on other arguments in this project. [Argument](first-lag.md)

I reconstructed the two enumerators by separating a single $(2k)$-cycle from an unordered pair of $k$-cycles. Distinguishing the cycle containing the largest label gives the binomial factor in the paper, which counts each unordered pair once. In particular the old row is $A_{2k-2}$ and the term added to the new Eulerian row is $\binom{2k-1}{k-1}tA_{k-1}^2$.

For $3\le k\le200$ I independently recomputed the Eulerian polynomials using the finite differences of integer powers. I evaluated the old polynomial and the two signed perturbations as exact rational numbers at both endpoints of every interval. This gave 118,206 strict endpoint signs in 19,701 intervals, together with the central checks at all 198 thresholds. The number of forced roots uses the gaps on both sides of the central root and the degrees of the pencils. [Independent checker](verify_first_lag_independent.py) · [Dyadic intervals](first-lag-prefix.jsonl.gz)

For $k\ge201$ I checked the ratio estimates in the two root ranges. The injection into ordered increasing runs gives the stated coefficient bounds. The three Rouché comparisons isolate the first $H$ roots, and subtraction of the geometric tails gives a derivative lower bound greater than $3/4$ in the scaled units. The Gaussian estimate for the product of the two short Eulerian rows and $4^{-j}\binom{2j}{j}\le1/\sqrt{j+1}$ then give (4). In the pole range the difference $D_{v+1}-\cos(\theta)D_v$ retains the factor $\sin(\theta)$ in both contributions, which is needed for the denominator estimate at the join. I checked the factorial cancellation in (8), the first-sample ordering, and the count $2H+(M-2H-1)=M-1$. The two ranges prove both pencil signs at every old root. I found no gap in this partial theorem. Formal status is ⬜ None.

To rerun the independent finite check, install Python with python-flint 0.9.0 and run the following from the repository root.

~~~sh
python3 -I -O topics/long-cycle-excedances/verify_first_lag_independent.py
~~~
