# Exact exterior certificate experiment

Run `python3 -I check.py > output.txt` to regenerate the complete [coefficient ledger](ledger.json.gz) and the [per-window report](output.txt). The ledger stores every coefficient in ascending degree, including padding zeros, for the original old and next enumerators and for each window's $T$ and $W$. It also stores each exact rational center and both endpoints. The report brackets $M(T)/a$ and $M(W)/a$ by rationals with denominator one million. Pass flags are computed from exact fractions before rounding.

The grid uses old sizes $12,24,40,64,96,128$, cutoffs in the distinct set $`\{3,7,\lfloor n/4\rfloor,n\}`$ and all ranks $1\le h\le\lfloor7\sqrt n/20\rfloor$. Both strict inequalities passed in all 47 windows across 23 pairs. The maximum $M(T)/a$ lies in $[46975,46976]/10^6$ and the maximum $M(W)/a$ lies in $[122246,122247]/10^6$.

The two row computations use independent cycle decompositions. The anchored recurrence chooses the support of the entire cycle containing the greatest label, with coefficient $\binom{n-1}{j-1}$ for cycle size $j$. The insertion recurrence either extends a cycle or adds a new minimum-length cycle. Both use the Eulerian cycle polynomial $tA_{j-1}(t)$. The two calculations agree on all intermediate rows used here. A third check enumerates permutations literally for $0\le n\le8$ and $`k\in\{2,3,7\}`$, matching all 27 rows.

The literal insertion identity with full lag $V$ is $Q=ntP+t(1-t)P'+V$. Thus for the specified $W$,

$$
W=(1-t)\bigl(tP'-(h+1)P+a t^h\bigr)+V.
$$

The checker compares both expressions coefficient by coefficient. For any $x<0$ in the modulus box, the definition of $M$ bounds $|R(x)|/|x|^h$, because the largest weight for a negative exponent is at the lower endpoint. The two-term error gives opposite old signs after normalization at the endpoints. At an old zero, $W(x)=Q(x)+(1-x)a x^h$, so $M(W)<a$ forces the strict sign $(-1)^{h+1}$ for the original successor value. Each passing window therefore supplies the sign witness under the stated criterion. These computations only assess the listed windows.
