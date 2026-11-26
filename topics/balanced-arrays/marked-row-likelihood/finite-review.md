# Independent review of the million-row sign certificate

Agent-assisted review by Codex (finite_sign_referee), 2026-11-26.

For the balanced-array polynomial at $n=1{,}000{,}000$, $d=250{,}000$, and $r=127{,}000$, the [finite proof](finite.md) and its exact certificates establish exactly 508,000 distinct negative roots. The coefficients count labeled zero-one arrays with common column quota and row sums at most $r$, as in the [original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#conjBalancedArrays). The cyclic construction supplies positive coefficients through degree $\lfloor nr/d\rfloor=508000$. The result establishes this instance of the universal conjecture.

## Mathematical checks

- The discarded overlap event depends only on the common and exclusive cell data. After conditioning separately on both marked masks, the two unmarked column subsets are independent and uniform at their sizes. The blue subset has size at least $k-1>(n-1)/2$ on every required path. The factorial-moment bound, union bound, and conversion to a tilt per unit difference all hold uniformly over the marked masks.
- The alternative [exact-odds comparison](binomial-odds.md) applies with exchangeable unmarked rows and the marked cell forbidden in both arrays. The one-mark pairing restriction is invariant under orientation. Its average retention factor follows from the hypergeometric sum and Vandermonde's identity. The positive source case gives common interval support across the compared indices, so the adjacent inequalities can be multiplied.
- Comparing singleton allocations in the two-column fiber gives the high-versus-low marked-column inequality. The covariance inequality then gives the lower bound on the conditional mean deficit. The equal-margin use of [Kahn and Neiman's orientation lemma](https://arxiv.org/pdf/1001.0610#page=9) gives log-concavity and interval support for the missing-cell size law. This yields the tail inequality, the bound for the deficit transform, and the stated curvature floor after telescoping the two paths of normalized insertion probabilities.
- The row-deficit bound follows from the expected availability estimate in the [upper-edge proof](../dense-regime/below-cap/finite-aspect/upper-edge/paper.pdf) and the identity between balanced saturation and missing-cell saturation. The [scalar marked-row recursion](../dense-regime/below-cap/finite-aspect/marked-row/recursion-review.md) supplies another lower bound on the indicated range. The [mixed-phase brackets](../dense-regime/below-cap/finite-aspect/marked-row/mixed-phase/README.md) bound the normalized log decrements. Upper minus previous lower has the correct sign and index for the cap contribution to the curvature ceiling.
- The five local curvatures bound the seven central magnitudes at the geometric radius. The [global orientation comparison](../orientation-normalization.md) orders those radii and gives outward decrease of term magnitudes. The alternating tails pair nonnegatively after distance three for the seven-term test, and after distance one for the factor-four test.
- The [earlier inner argument](../dense-regime/below-cap/finite-aspect/marked-row/README.md) supplies strict alternating signs at the same radii through 506470. The upper-edge proof supplies the signs from 507905 through 507999, because its factor-nine test persists as the quota increases. The new replay covers 506471 through 507905, with one overlapping center. The signs at zero, all internal centers, and toward negative infinity give 508,000 disjoint intervals containing roots. The degree implies all these roots are simple.

## Exact replays

Run from this folder.

~~~sh
python3 -IB verify-finite.py
python3 -IB verify-finite.py --exact-odds
python3 -IB ../dense-regime/below-cap/finite-aspect/upper-edge/verify.py
~~~

Both finite modes passed on a fresh run. Each checked 330 seven-term signs at centers 506471 through 506800 and 1,105 factor-four signs at centers 506801 through 507905.

| Replay | Minimum seven-term margin exceeds | Minimum factor-four log curvature exceeds |
| --- | ---: | ---: |
| Concentration | 0.0065317 at 506611 | 1.3941817 at 506801 |
| Exact odds | 0.0132366 at 506594 | 1.4101059 at 506801 |

The upper-edge replay confirmed 507905 as the first center of its certified outer interval. I checked the outward integer rounding for binomial masses, the omitted-mass bound, reciprocal interval directions, rational upper-tilt witnesses, and logarithm and exponential remainder bounds. The two finite modes share the mixed-phase bracket implementation and the endpoint proofs.

I found no substantive mathematical or computational gap. This review uses the earlier inner signs as a reviewed dependency and does not rerun the earlier inner endpoint checker. The available Lean results check some of the overlap and pairing calculations. The finite sign certificate and root conclusion remain outside the formal coverage.
