"""Compute Z independently from the two lattice path boundaries and ranked flats."""
import argparse
from itertools import combinations,product
from math import comb
from pathlib import Path
import json


def ribbon_ranks(word):
    if any(s not in 'EN' for s in word):
        raise ValueError('encode the inner path with E and N')
    upper='N'+word+'E'
    lower='E'+word+'N'
    n=len(upper)
    left=[i for i,c in enumerate(upper) if c=='N']
    right=[i for i,c in enumerate(lower) if c=='N']
    # Bases are precisely the increasing r-tuples bounded coordinatewise by
    # the North-step positions of the upper and lower paths. For rank(S) use
    # the maximum cardinality of an ordered matching into these intervals.
    ranks=[]
    for mask in range(1<<n):
        pos=0
        size=0
        for lo,hi in zip(left,right):
            pos=max(pos,lo)
            while pos<=hi and not (mask>>pos)&1:
                pos+=1
            if pos<=hi:
                size+=1
                pos+=1
        ranks.append(size)
    return ranks


def graph_ranks(vertices,edges):
    ranks=[]
    for mask in range(1<<len(edges)):
        parent=list(range(vertices))
        def find(i):
            while parent[i]!=i:
                i=parent[i]
            return i
        rank=0
        for j,(u,v) in enumerate(edges):
            if mask & (1<<j):
                u,v=find(u),find(v)
                if u!=v:
                    rank+=1
                    parent[u]=v
        ranks.append(rank)
    return ranks


def z_from_ranks(rank):
    """Use KL degree bound and Z-palindromicity separately on every interval."""
    top=len(rank)-1
    flats=set()
    for f,r in enumerate(rank):
        complement=top^f
        while complement:
            bit=complement & -complement
            if rank[f|bit]==r:
                break
            complement-=bit
        else:
            flats.add(f)
    if 0 not in flats:
        raise ValueError('expected a loopless matroid')
    kl={top:(1,)}
    if top==0:
        return (1,)
    for f in sorted(flats-{top},reverse=True):
        d=rank[top]-rank[f]
        partial=[0]*(d+1)
        rest=top^f
        s=rest
        while s:
            g=f|s
            if g in flats:
                i=rank[g]-rank[f]
                for j,c in enumerate(kl[g]):
                    partial[i+j]+=c
            s=(s-1)&rest
        kl[f]=tuple(partial[d-i]-partial[i] for i in range((d+1)//2))
        for i,c in enumerate(kl[f]):
            partial[i]+=c
        if partial != partial[::-1] or any(c < 0 for c in kl[f]):
            raise ArithmeticError(f'Invalid contraction coefficients at flat {f}')
        if f==0:
            return tuple(partial)
    raise AssertionError('missing empty flat')


def narayana(rank):
    return tuple(comb(rank+1,k)*comb(rank+1,k+1)//(rank+1) for k in range(rank+1))


def words():
    for n in range(2,13):
        for w in product('EN',repeat=n-2):
            yield ''.join(w)
    yield from ('NENENENENEN','NNEENNENNEEE','EENNNNEENNEEE','NNENENNEENENN')


def record(word):
    ranks = ribbon_ranks(word)
    rank = ranks[-1]
    coefficients = z_from_ranks(ranks)
    return dict(inner_word=word, n=len(word) + 2, rank=rank,
                coefficients=list(coefficients), method='ordered interval rank and flat recursion',
                equals_narayana=coefficients == narayana(rank))


def verify_archive(path):
    expected = set(words())
    with path.open() as archive:
        for line_number, line in enumerate(archive, start=1):
            archived = json.loads(line)
            word = archived['inner_word']
            if word not in expected:
                raise ValueError(f'Duplicate or unexpected word on line {line_number}')
            calculated = record(word)
            if archived != calculated or not calculated['equals_narayana']:
                raise ValueError(f'Coefficient discrepancy on line {line_number} for {word!r}')
            expected.remove(word)
    if expected:
        raise ValueError(f'Archive missing {len(expected)} words')
    print(f'Verified all {sum(1 for _ in words())} ribbon records.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    archive = Path(__file__).resolve().parents[1] / 'results' / 'ribbons.jsonl'
    parser.add_argument('--archive', type=Path, default=archive)
    parser.add_argument('--verify', action='store_true', help='recompute and compare every record')
    args = parser.parse_args()
    if args.verify:
        verify_archive(args.archive)
        return
    seen = set()
    if args.archive.exists():
        seen = {json.loads(line)['inner_word'] for line in args.archive.read_text().splitlines()}
    with args.archive.open('a', buffering=1) as out:
        for word in words():
            if word not in seen:
                out.write(json.dumps(record(word), separators=(',', ':')) + '\n')


if __name__ == '__main__':
    main()
