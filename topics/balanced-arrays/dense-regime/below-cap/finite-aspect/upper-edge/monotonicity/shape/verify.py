"""Exact scalar identities and two finite enumerations of the labeled row statistic."""
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
from math import comb
from pathlib import Path
import gzip
import json
import sys


def check_scalar(d, r, x):
    c = d-r
    weights = [comb(d, r-j)*x**j for j in range(r+1)]
    total = sum(weights)
    p = weights[0]/total
    t = sum(j*v for j, v in enumerate(weights))/total
    variance = sum((j-t)**2*v for j, v in enumerate(weights))/total
    u = 1-(1+t)*p
    poly = (d+1)*t*t - (r*c+(r-2*c)*t+d*t*t)*u - c*t*u*u
    gp = t*p/variance - 1/(1+t)**2
    assert (1+x)*variance == t+c*u
    assert poly == gp*(1+t)**2*(r-t)*(t+c*u)
    if t*t <= Q(r*c,d):
        assert gp > 0
    return (gp > 0)-(gp < 0)


@lru_cache(maxsize=None)
def count(n, margins, r):
    """Remove one specified labeled row and sum over its possible subsets."""
    d = len(margins)
    if margins[0] < 0 or margins[-1] > n or sum(margins) > n*r:
        return 0
    if not any(margins):
        return 1
    result = 0
    for j in range(r+1):
        for cols in combinations(range(d), j):
            m = list(margins)
            for h in cols:
                m[h] -= 1
            result += count(n-1, tuple(sorted(m)), r)
    return result


@lru_cache(maxsize=None)
def corank_one(n, margins, r):
    """Exclude rows occupied in all columns via inclusion-exclusion."""
    assert r+1 == len(margins)
    if margins[0] < 0 or margins[-1] > n:
        return 0
    result = 0
    for h in range(min(margins)+1):
        term = (-1)**h*comb(n,h)
        for v in margins:
            term *= comb(n-h,v-h)
        result += term
    return result


def excess_record(n, d, r, s, counter):
    k, ell = divmod(n*r-s,d)
    margins = (k,)*(d-ell)+(k+1,)*ell
    arrays = counter(n,margins,r)
    marked = 0
    for subset in combinations(range(d),r):
        m = list(margins)
        for i in subset:
            m[i] -= 1
        marked += counter(n-1,tuple(sorted(m)),r)
    active_sum = n*(arrays-marked)
    error = Q(active_sum,arrays)-(Q(n*s,n+s-1) if s else 0)
    return dict(n=n,d=d,r=r,s=s,arrays=arrays,active_sum=active_sum), error


def finite_cases():
    cases = {(n,d,r) for n in range(2,13) for d in range(2,6) for r in range(1,d)}
    cases.update((n,d,d-1) for n in (16,32,64) for d in (3,5,8))
    rows = []
    failures = []
    scale_failures = []
    for n,d,r in sorted(cases):
        errors = []
        for s in range(n*r+1):
            counter = corank_one if r==d-1 else count
            record, value = excess_record(n,d,r,s,counter)
            if r==d-1 and n<=12:
                assert (record,value)==excess_record(n,d,r,s,count)
            if r==1:
                assert value==Q(s*(s-1),n+s-1)
            if s>1 and d*s*s<=n*n*r*(d-r) and value<=errors[-1]:
                scale_failures.append((n,d,r,s-1))
            rows.append(record)
            errors.append(value)
        for residue in range(d):
            vals = errors[residue::d]
            signs = [(a<b)-(a>b) for a,b in zip(vals,vals[1:]) if a!=b]
            if any(x<y for x,y in zip(signs, signs[1:])):
                failures.append((n,d,r,residue))
    return rows,sorted(cases),failures,scale_failures


def main():
    odds = [Q(2)**i for i in range(-12,13)]
    probes = 0
    for d in range(2,31):
        for r in range(1,d):
            signs = [check_scalar(d,r,x) for x in odds]
            assert signs==sorted(signs,reverse=True)
            probes += len(signs)
    rows,cases,failures,scale_failures = finite_cases()
    result = dict(fibers=rows,fixed_phase_valleys=failures,
                  scale_one_nonstrict_steps=scale_failures)
    archive = Path(__file__).with_name('finite-checks.json.gz')
    if sys.argv[1:]==['--write']:
        archive.write_bytes(gzip.compress((json.dumps(result,separators=(',',':'))+'\n').encode(),mtime=0))
    else:
        assert not sys.argv[1:]
    assert json.loads(gzip.decompress(archive.read_bytes()))==result
    print(probes,'exact rational scalar probes;',len(rows),'labeled fibers in',len(cases),'triples')
    print(len(failures),'fixed-phase valleys;',len(scale_failures),'nonstrict positive-slack steps at scale one')
    if failures:
        print('First finite valley:',failures[0])
    if scale_failures:
        print('First finite scale-one obstruction:',scale_failures[0])


if __name__=='__main__':
    main()
