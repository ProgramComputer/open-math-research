# Centered signs for all cutoffs above seven

For $n\ge10000$, $k\ge8$ and $n\ge48k$, this proposed theorem would give both [centered phase inequalities](../fourier-centered/README.md) at every height $s\ge0$ with $n\pi^2\ge s^2+\pi^2$. At a zero of the original strict-excedance enumerator, the original successor row would therefore have the sign of the principal sine. The finite and unbounded cutoff ranges use the same contour normalization and conjugate-pairing argument. [Original-row statement](RepositoryAllWideCenteredRows.lean)

The composition passed a local Lean 4.19 check with the original numerator and contour interfaces supplied as explicit hypotheses. Its production replay is pending. On Linux, run `python3 -Bu check.py /path/to/fresh/project` in this directory.
