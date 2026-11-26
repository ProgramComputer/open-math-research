# Strict peaks by appending a legal Catalan letter

Screened November 26, 2026. The catalog defines strict peaks as $`w_{i-1}<w_i>w_{i+1}`$, with $`w_1=0`$ and $`0\le w_{i+1}\le w_i+1`$. It attributes the exact theorem (simple negative roots and strict consecutive interlacing for all lengths) to ProgramComputer's analytic proof with finite exact checks, reports Lean coverage for the counting definition, and explicitly lists a non-analytic proof as unknown. A distinct local recurrence proof would replace the analytic regime and separate finite check with a uniform combinatorial argument. [Author catalog](https://www.symmetricfunctions.com/realRootedCatalan.htm#catalanWordPeaksRealRooted)

The earlier research note supplies the shifted coefficient formula and a two-lag differential recurrence, and identifies the unproved inverse-Euler positivity step. It also lists a possible matching representation. The appended-letter recurrence below is a distinct approach. The generating function is known from Baril–Harris–Harry–McClinton–Ramírez, Theorem 18. Indexed web/arXiv variants included “Catalan words strict peaks Alexandersson recurrence final height interlacing site:github.com”, “Catalan words peaks Alexandersson real rooted site:x.com”, and “Catalan words strict peaks Alexandersson recurrence combinatorial real rootedness arxiv”. No exact local recurrence proof surfaced. Direct X search redirected to login. This covers the two requested primary pages and public indexed hits. [Earlier research note](https://github.com/1337isnot1337/solved-conjectures/blob/main/docs/alexandersson-catalan-peaks-research.md) · [Enumerative paper](https://doi.org/10.26493/2590-9770.1794.fc5)

The [proof-method follow-up on issue #3](https://github.com/ProgramComputer/open-math-research/issues/3#issuecomment-7191895944) records the scope. The obstructions below concern intermediate states in one recurrence. The [all-length theorem for the summed polynomial](../README.md) is already proved.

## Exact strict-drop obstruction

Write $`R_{n,h}`$ for words ending at height $`h`$ whose last step rose, $`F_{n,h}`$ for the other words, and $`U_{n,k}=\sum_{h\ge k}(F_{n,h}+tR_{n,h})`$. A drop marks a peak exactly if the last step rose. Therefore, with out-of-range terms zero,

$$
R_{n+1,k}=F_{n,k-1}+R_{n,k-1}, \qquad
F_{n+1,k}=F_{n,k}+R_{n,k}+U_{n,k+1}
$$

starting at $`F_{1,0}=1`$. The first two terms of $`F_{n+1,k}`$ count ties. The suffix $`U_{n,k+1}`$ counts every legal strict drop into height $`k`$.

The single-height marked drop at $`n=4,h=1`$ is $`2+2t+t^2`$. Even after summing every legal source height, the strict-drop contribution into height five at length sixteen is

$$
U_{15,6}=19791+75285t+96525t^2+46635t^3+6795t^4+126t^5.
$$

It has a constant last Sturm polynomial and variations $`4,1`$ at $`-\infty,+\infty`$, hence only three real roots. This refutes a real-rootedness invariant for strict-drop sums with their actual legal weights. Adding the ties yields $`F_{16,5}=66255+207069t+211053t^2+78755t^3+8775t^4+126t^5`$, with variations $`5,0`$. An induction for the full transitions could exploit this compensation.

## Consecutive full-state obstruction

Already $`F_{4,0}=2+3t`$ and $`F_{5,0}=5+8t+t^2`$ fail consecutive interlacing at fixed height. The latter has two distinct real roots, and its value at the single root $`-2/3`$ of the former is $`1/9>0`$, placing it outside the root interval. Height zero admits no final rise, so $`R_{n+1,1}=F_{n,0}`$ transfers the obstruction to fixed-height rise states. This does not determine the interlacing of complete row polynomials, which use all heights.

## Independent exact check

Use Dyck height just before up-step number $`i`$ as the letter $`w_i`$. A rise into a letter occurs when its up-step immediately follows the preceding up-step. A strict drop into the next letter occurs when at least two down-steps intervene before its up-step. Therefore a Dyck-step counter can mark each peak when it appends the new up-step, tracking whether the previous up-step was consecutive and capping the pending down-step count at two. To count $`U_{15,6}`$, stop at the sixteenth up-step, require pre-step height five and at least two pending down-steps, then append the forced down-step suffix. To count $`F_{16,5}`$ allow one pending down-step as well. This independently gives both degree-five vectors and the height-zero vectors at lengths four and five.

For the root counts the alternative checker reflects the variable and partitions the positive axis at rational cutpoints. The endpoint signs give a lower bound by continuity. A fractional-linear substitution on each bounded interval, and a translation on the final ray, give matching upper bounds by Descartes' rule of signs. The resulting counts are three and five respectively. The height-zero quadratic has discriminant 44 and evaluates to $`1/9`$ at $`-2/3`$.

The append-state derivation and the alternative path and sign calculation were independently checked with agent assistance. No Lean or Rocq coverage is claimed for these obstructions.

```sh
python3 -B catalan-append-peaks.py
python3 -B independent-path-check.py
```
