# Adding one label to an accepted color assignment

Fix a minimum cycle length $k\ge2$. Let $C_{n,p}$ be the number of accepted pairs of a word and a permutation of its $p$ colors, divided by $p!$. Let $E_{n,k}$ be the strict-excedance enumerator of the original permutations. The [color transform](README.md) identifies $C_{n,p}$ with the coefficient of $t^p$ in $E_{n,k}(t)/(1-t)^n$.

For $n+1\ge k$ write $m=n+1-k$. The change on adjoining one label is exactly

$$
C_{n+1,p}-pC_{n,p}
=\binom{n}{k-1}\sum_{j=1}^p j^{k-1} C_{m,p-j}.
$$

Here $C_{0,0}=1$ and $C_{0,p}=0$ for positive $p$. For $p\ge1$, dividing by $p^{n+1}$ gives the increase in the acceptance probability. The $j=p$ term matters when $n=k-1$.

Bowen Zuo formalizes a broader weighted binomial jump in the accompanying sources of his minimum-cycle descent project. Here the probability jump above is the unweighted $u=0$ specialization. Zuo also identifies the occupancy probability with the corresponding original excedance-row coefficient in the transformed label basis. The modules here connect the unweighted identity to the literal insertion lag and the repository's common-pin exterior estimates. [Zuo’s occupancy identification](https://github.com/AlexZander-666/cycle-minimum-descent-real-roots/blob/e632c19bc246b819cd6b882cbf22c2fa9bc453de/formal/LongCycleBounds/OccupancyVerified.lean#L142-L146) · [Zuo’s weighted binomial jump](https://github.com/AlexZander-666/cycle-minimum-descent-real-roots/blob/e632c19bc246b819cd6b882cbf22c2fa9bc453de/formal/LongCycleBounds/OccupancyBinomialJump.lean#L143-L148)

## Counting newly accepted pairs

Appending any color to an accepted word preserves acceptance, giving exactly $p$ extensions. A newly accepted pair has exactly one cycle of colors that received too few labels before the extension. It contained $k-1$ old labels and the new letter lands in it. If it contains $j$ colors, choose them in $\binom pj$ ways and order the cycle in $(j-1)!$ ways. Choose the old labels in $\binom n{k-1}$ ways, assign them to the cycle in $j^{k-1}$ ways, and choose the new label’s color in $j$ ways. Multiply by the accepted count $(p-j)! C_{m,p-j}$ on the complement. Dividing by $p!$ gives exactly the displayed summand.

## The polynomial lag

Write $A_{k-1}$ for the ordinary Eulerian polynomial and $L=\binom n{k-1}tA_{k-1}E_{m,k}$ for the full lag summand in the unnormalized insertion recurrence. Put $F_n=E_{n,k}/(1-t)^n$. Differentiation gives

$$
F_{n+1}-tF_n'=L/(1-t)^{n+1}.
$$

All coefficients of $L$ are nonnegative and the constant coefficient of $(1-t)^{-(n+1)}$ is one. Hence

$$
0\le [t^p]L\le C_{n+1,p}-pC_{n,p}.
$$

This reduces the near-rank lag bound in the [exterior-root proof](../effective-front.md) to a bound on the same acceptance increment. Its smallness relative to the old coefficient remains a uniform quantitative obligation. [Formal power-series proof](ColorInsertion.lean) · [Theorems for the original permutation rows](RepositoryColorInsertion.lean)

The independent finite calculation enumerates every word and color permutation at old sizes through 6 with $1\le p\le4$ and $2\le k\le\min(6,n+1)$. It counts the newly accepted pairs separately for each cycle size $j$ and checks lag domination against coefficients obtained by direct permutation enumeration. Rerun with `python3 -I verify_successor.py`. All 80 adjacent-size triples and all 200 marked cycle-size comparisons passed. [Checker](verify_successor.py) · [Output](successor-output.txt)
