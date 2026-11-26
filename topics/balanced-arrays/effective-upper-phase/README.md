# Effective Gaussian leading signs near the largest quota

For every $d\ge10^{12}$, $n\ge64d$ and proper row cap $1\le r<d$, the two levels $k=D-1,D-2$ with $D=\lfloor nr/d\rfloor$ occur as principal Gaussian phase crossings. At either crossing the real part of the sum of all Gaussian angular leading terms has strict sign $(-1)^k$. Transverse approximation and localization errors still need bounds to obtain a sign of the balanced-array polynomial. [Proof](proof.md) · [Agent-assisted independent review](review.md)

The finite rational probes test a separate phase-alignment and Gaussian-branch criterion. Their 51 sampled records contain 32 crossing witnesses and 96 retained positive labels. The full search ledger contains all 161 evaluations, including failed sufficient tests and repeated evaluations. Failed tests do not exclude crossings, and the finite probes certify neither a sum over discarded labels nor an actual root. [Sampled records](finite-angular-phase.jsonl) · [Search ledger](finite-angular-phase-search.jsonl)

Run from this directory with Python 3 and no third-party dependencies.

~~~sh
python3 -I -B finite-angular-phase.py
~~~

The default command repeats the exact-rational evaluations and checks both archives byte for byte. Use the same command with an added argument of `--write` to regenerate them.
