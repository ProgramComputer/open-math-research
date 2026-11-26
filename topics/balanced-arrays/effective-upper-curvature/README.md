# Effective upper-edge curvature for balanced arrays

For finite labeled balanced arrays, a nonasymptotic coefficient inequality gives strict alternating signs at a terminal interval of geometric radii. A stronger curvature test separates the outer negative roots by a circle and proves their simplicity. These criteria apply to the actual capped polynomial. The effective cutoff for real-rootedness of the full polynomial remains unknown. [Proof](proof.md) · [Agent-assisted review including the separating-circle proof](review.md)

| Parameters $(n,r,d)$ | Distinct outer roots by integer conditions | Simple outer roots by integer conditions | Distinct outer roots by rational bound | Simple outer roots by rational bound |
| --- | ---: | ---: | ---: | ---: |
| $(20{,}000,10,20)$ | 1 | 1 | 4 | 3 |
| $(10^8,50,100)$ | 24 | 15 | 64 | 42 |

All counts are lower bounds from sufficient criteria. The replay evaluates the original integer conditions and the sharpened rational tests at eleven parameter triples. The two examples in the table use only these criteria and do not compute the full polynomial. [Exact archived witnesses](upper-curvature-cases.jsonl)

The regular-row two-column estimate has its own [agent-assisted review](regular-margin-ratio-review.md) and [primary-source comparison](regular-margin-ratio-prior.md). The latter credits the Borcea–Brändén–Liggett negative-dependence results and Liebenau–Wormald switching identities.

**Formal verification.** ⬜ None.

From this directory, run with Python 3 and no third-party dependencies.

~~~sh
python3 -I -B upper-curvature-cases.py
~~~

The default command checks the exact archive. Add --write to regenerate it.
