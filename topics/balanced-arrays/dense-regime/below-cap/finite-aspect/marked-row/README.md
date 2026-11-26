# Signs of balanced arrays from one marked row

With one million rows, 250,000 columns and row cap 127,000, **506,565 of the 508,000 roots are simple and negative**. In order of absolute value these are the first 506,470 and the last 95. The intervening annulus has exactly 1,435 roots, counted with multiplicity. Their types remain open. [Marked-row proof](paper.pdf) · [Extension through quota 506,470](mixed-phase/README.md) · [LaTeX source](paper.tex) · [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays)

## Finite sign test

At equal column sums $`K`$ in $`n`$ rows, let $`e(n,K)`$ be the probability that a row is saturated, conditional on a zero in a specified column. The marked row has a size distribution that can be bounded by ordinary binomial distributions truncated at the cap. Removing the marked row gives a recursion, so all the certificate calculations use one-dimensional probabilities.

Suppose $`n\ge10^6`$, $`n/4\le d\le n/2`$, $`1/8\le k/n\le7/8`$, and the required margins are feasible through $`k+2`$. If $`l\le e(n,k-2)`$ and $`e(n,k+2)\le h<1`$ with $`4d(h-l)\le1-h`$ and $`l\ge0`$, then at $`v_k=\sqrt{a_{k-1}/a_{k+1}}`$ the sign of $`P(-v_k)`$ is $`(-1)^k`$. The open and closed disks both contain exactly $`k`$ roots. The manuscript also gives a sharper test using the seven central coefficient bounds.

For the example above, 270 blocks satisfy the variation bound and 51 more single quotas satisfy the sharper test, following the initial interval through 504,158. The previous disk and row-deficit tests gave 502,482 simple negative roots. These bounds account for 3,274 additional roots. Tracking each step as the columns change quotas adds a further 809, each checked by two independent implementations. [Proof and checks for the additional 809 quotas](mixed-phase/README.md) [Earlier bounds](../upper-edge/README.md) · [Rational witnesses](quota-blocks.json)

The recursion also bounds changes in the log probabilities of respecting the cap. At fixed positive dimension-to-height ratio and interior column density, the variation over each fixed quota window tends to zero when the mean unrestricted row load lies more than a diverging multiple of $`\sqrt d`$ below the cap. This gives a direct route to the angular Gaussian profile there. The earlier general theorem already gives eventual geometric signs on a wider range. [Recursive estimate](recursion-review.md) · [Earlier sign theorem](../../../../effective-sublinear/angular-theorem.md)

**Formal verification**　⬜ None. Independent agent-assisted reviews checked the row comparison, the sign calculation, and the asymptotic recursion. Separate integer implementations checked the stated finite endpoint. [Mathematical review](review.md) · [Two-sided comparison and prior work](literature.md) · [Independent numerical verification](independent/README.md)

~~~sh
python3 -IB verify.py
python3 -IB independent/verify.py
tectonic paper.tex
~~~

The main checker replays only rational arithmetic. To regenerate its block choices and trial tilts, run `python3 -IB verify.py --generate`. That mode uses floating point to propose rational trial parameters and certifies every proposal by integer inequalities before writing the witness file.
