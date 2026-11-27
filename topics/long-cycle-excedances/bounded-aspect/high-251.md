# High-angle middle signs from size 251

For $`n\ge251`$, $`4\le n/k\le20`$, and $`nS^2\ge6/5`$, the high-angle argument in the [grouped proof](grouped-proof.md) gives the alternating integer-phase signs and the prescribed sign of the actual next row at each old zero whenever $`kS\ge7`$. The table gives lower local entrances.

| Aspect | Entrance for $`k\le100`$ | Entrance for $`k\ge100`$ |
| --- | ---: | ---: |
| $`[4,15/2]`$ | 7 | 7 |
| $`[15/2,10]`$ | 5 | 5 |
| $`[10,14]`$ | 5 | 6 |
| $`[14,18]`$ | 5 | 6 |
| $`[18,20]`$ | 5 | 6 |

The only changed probability constant is $`kd_r\le61/100`$ for $`r\ge2k`$. Here $`k\ge\lceil251/20\rceil=13`$ and the sufficient tangent and induction conditions become $`1/13+\log(100/61)<61/100`$ and $`1+\log2+(1+61/100)/13<3(61/100)`$. The old lower probability bound $`kd_r>547/1000`$ for $`r\ge3k`$ still applies. Both kernel powers adapt to the guaranteed distinguished degree and all signed pole tails come from the same integrals. The least disk margin exceeds $`9563/10^6`$.

Replay all ten fixed boxes with `python3 -I -B high-251.py`. [Checker](high-251.py) · [Output](high-251-output.txt)
