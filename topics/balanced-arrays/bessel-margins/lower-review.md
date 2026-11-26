# Source check for the prescribed-profile lower bound

The research orchestrator independently compared the lower bound with Gurvits's coefficient theorem and its elementary extraction proof. The result agrees with that source. The balance capacity is one by Jensen, since the prescribed row sizes make every column mean $k$. The polynomial is homogeneous and real stable, has nonnegative coefficients, and has degree at most $n$ in each variable. Hence the degree-dependent univariate extraction factor applies successively in the first $d-1$ variables. Once these margins have been extracted, homogeneity fixes the final margin without an additional binomial factor. [Gurvits, Theorem 5.1 and §7](https://eccc.weizmann.ac.il/report/2013/141/revision/1/download/)

The orchestrator also checked the elementary factor using the matching-mean binomial atom bound for a sum of independent Bernoulli variables. The extremal exponent or deterministic case follows directly by taking the appropriate boundary capacity. In the interior, tilting at the positive capacity minimizer supplies the needed mean without changing real-rootedness. [Hoeffding, Theorem 5](https://repository.lib.ncsu.edu/bitstream/1840.4/2268/1/ISMS_1955_128.pdf)

For the explicit error, Robbins's bounds give a log remainder at least $-1/(12k)-1/(12(n-k))=-1/[12n x(1-x)]$ for the mean atom. On $x\in[1/5,4/5]$ this is at least $-25/(48n)$. Raising to power $d-1$ gives exactly the lower factor used in the consequences. The check establishes applicability and normalization of the existing capacity theorem. [Robbins’s Stirling bounds](https://heuklyd.github.io/papers/pdf/Robbins-1955.pdf)

Recorded as an agent-assisted independent comparison by the research orchestrator, 2026-11-26.
