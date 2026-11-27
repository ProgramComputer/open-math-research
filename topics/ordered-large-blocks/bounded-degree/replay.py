"""Replay stored rational rectangles and root brackets, without a root solver."""

import sys
import json
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
from finitej import bounds_constants, coeff_intervals, sign, value, seam


def check(path):
    data = json.loads(Path(path).read_text())
    d, J = data["d"], data["J"]
    bounds_constants(d)
    events = defaultdict(list)
    special = ordinary = 0
    for cell in data["cells"]:
        cl, ch, hl, hh = map(F, cell[:4])
        assert d <= cl < ch <= d + 1 and 0 <= hl < hh <= F(1, J)
        events[cl].append((hl, hh, 1))
        events[ch].append((hl, hh, -1))
        A, B = coeff_intervals(d, cl, ch, hl, hh, J)
        assert len(cell[-1]) == d
        last = F(-1)
        for i, (sa, sb, mode) in enumerate(cell[-1]):
            a, b = F(sa), F(sb)
            assert 0 <= a < b <= 1 and last < a
            last = b
            assert sign(value(A, a, a), (-1) ** i)
            if mode == "seam":
                assert i == d - 1 and b == 1 and seam(A, B, cl, ch, hh, a)
                special += 1
            else:
                assert mode == "ordinary"
                assert sign(value(A, b, b), (-1) ** (i + 1))
                assert sign(value(B, a, b), (-1) ** (i + 1))
                ordinary += 1
    xs = sorted(events)
    assert (xs[0], xs[-1]) == (d, d + 1)
    active = defaultdict(int)
    for c in xs:
        for a, b, v in events[c]:
            active[a, b] += v
        active = {k: v for k, v in active.items() if v}
        if c < xs[-1]:
            u = F(0)
            for (a, b), count in sorted(active.items()):
                assert count == 1 and a == u, (a, b, u, count)
                u = b
            assert u == F(1, J)
        else:
            assert not active
        active = defaultdict(int, active)
    print(d, J, len(data["cells"]), ordinary, special)


if not __debug__:
    raise SystemExit("Run the checker with Python assertions enabled.")

if __name__ == "__main__":
    for name in sys.argv[1:]:
        check(name)
