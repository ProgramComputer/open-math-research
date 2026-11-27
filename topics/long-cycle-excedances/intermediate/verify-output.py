"""Check coverage counts and per-threshold certificate records."""
from collections import defaultdict
from pathlib import Path
import re

from entrance import entrance
from check import phase_point

if not __debug__:
    raise SystemExit('Run without -O so every certificate assertion is checked.')


expected = defaultdict(lambda:[0,0,0])
gaps=set()
for n in range(251,1001):
    for k in range(max(7,n//20+1),n//4+1):
        h,j=entrance(n,k)
        r=j-h-1
        expected[k][0]+=1
        expected[k][1]+=r
        expected[k][2]+=r>0
        gaps.update((n,q) for q in range(h+1,j))
for n,j in gaps:
    assert phase_point(n,j).upper()<phase_point(n,j+1).lower(),(n,j)
text=Path("output.txt").read_text()
actual={}
for k, token, pairs, ranks, sampled, fallbacks in re.findall(
    r"^digest k=(\d+): ([0-9a-f]{64}), metrics \((\d+), (\d+), (\d+), (\d+)\)$",
    text,
    re.M,
):
    key=int(k)
    assert key not in actual
    actual[key]=[int(pairs),int(ranks),int(sampled)]
    assert 0<=int(fallbacks)<=int(ranks)
assert actual==expected
sums=[sum(record[j] for record in expected.values()) for j in range(3)]
assert sums==[93902,541199,82395],sums
assert text.splitlines()[-1].startswith("TOTAL pairs=93902 sampled=82395 ranks=541199 ")
print("Complete coverage confirmed for all 93,902 pairs, including 541,199 certified finite gaps.")
