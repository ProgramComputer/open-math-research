from collections import Counter
from itertools import permutations


def cycle_lengths(permutation):
    unseen = set(range(len(permutation)))
    while unseen:
        start = i = min(unseen)
        length = 0
        while i in unseen:
            unseen.remove(i)
            length += 1
            i = permutation[i]
        assert i == start
        yield length


def rows(n, cutoff):
    descents, excedances = Counter(), Counter()
    for p in permutations(range(n)):
        if min(cycle_lengths(p)) >= cutoff:
            descents[sum(a>b for a,b in zip(p,p[1:]))] += 1
            excedances[sum(i<a for i,a in enumerate(p))] += 1
    return (tuple(r[i] for i in range(n)) for r in (descents,excedances))


for n,k in [(4,2),(5,3),(5,4),(5,5),(6,4),(6,5),(6,6)]:
    d,e=rows(n,k)
    value=sum(c*(-1)**r for r,c in enumerate(d))
    print(n,k,d,e,value)
    if n==4:
        assert d==(0,4,4,1)  # t(t+2)^2
    if n==5:
        assert d==(0,6,12,6,0)
        assert e==(0,1,11,11,1)
    if n==6:
        assert d==(0,9,53,47,11,0)
        assert value==8
