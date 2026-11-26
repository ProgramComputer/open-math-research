# Independent check of the backward multiplier obstruction

Agent-assisted review · 2026-11-26

The direct multiplier witness checks for $(n,r,d)=(7,2,4)$. I reconstructed the labeled counts in two ways without using the archived vectors as computational input.

First, for each quota $k$ I assigned one $k$-subset of the labeled rows to each of the four columns and counted states of the full row-load vector. A transition adding a column is allowed precisely when none of its chosen rows already has load two. This enumerates each admissible array once.

Second, label the $k$ occupied positions in each column. Rows holding two occupied positions pair labels of distinct colors, giving a matching in the complete four-partite graph with $k$ vertices per color. A matching of size $p$ leaves $4k-p$ distinct blocks, which can be injected into the labeled rows in $(n)_{4k-p}$ ways. Dividing by $(k!)^4$ removes the labels. For the matching count, after processing $c$ colors a matching of size $p$ leaves $ck-2p$ old vertices free. Exactly $\binom{ck-2p}{i}(k)_i$ choices attach $i$ of them to the next color. The two methods reproduce both vectors stated in the note.

I formed the image of $(1+q)^4$ over the rationals, cleared the positive denominator, and computed the value and both derivatives of the primitive integer polynomial at $-1$. They are $790934,-2137538,30418788$. The Laguerre expression is strictly negative, $-19490184966548$. This proves failure of the proposed diagonal map as a universal real-rootedness preserver on the negative-rooted input $(1+q)^4$. The deterministic row-deletion implication on the balanced-array family remains open. [Exact independent computation](check_witnesses.py)

The archived screen regenerated all 360 symbols from the source-range coefficients and matched the exact Sturm reports, giving 225 failures and 135 real-rooted symbols. [Archive replay](verify_archive.py)
