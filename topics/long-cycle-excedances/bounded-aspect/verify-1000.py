"""Replay the explicit n>=1000 aspect and angle cover."""
from fractions import Fraction as F
from math import isqrt
from multiprocessing import Pool
from pathlib import Path
from runpy import run_path

M=run_path(str(Path(__file__).with_name('check-grouped.py')))
N=1000

# Each row contains both high-angle entrances, for k<=100 and k>=100.
ASPECT = [
    ('15/2','10','9/2','5'),
    ('10','14','9/2','11/2'),
    ('14','18','4','11/2'),
    ('18','20','4','11/2'),
]

def check(task):
    l,X,p,q,k0,k1,low = task
    value=M['margin'](N,l,X,p,q,k0,k1,low)
    if value<=0:
        raise ArithmeticError(task+(str(value),))
    return int(10**6*value)

def tasks():
    prior=F(15,2)
    for l,X,a,b in ASPECT:
        l,X,a,b=map(F,(l,X,a,b))
        assert l==prior and l<X
        for A,k0,k1 in ((a,None,100),(b,100,None)):
            A0=F(isqrt(int(10000*max(F(6*N,5*X*X),F(6*(k0 or 0),5*X)))),100)
            assert A0>0 and A0<=A
            yield l,X,A,A,k0,k1,False
            p=A0
            while p<A:
                q=min(A,F(1,2)+F(int(2*p),2))
                assert q>p
                yield l,X,p,q,k0,k1,True
                p=q
        prior=X
    assert prior==20

if __name__=='__main__':
    if not __debug__:
        raise SystemExit('Run without -O.')
    M['constants']()
    specs=list(tasks())
    with Pool(6) as pool:
        for spec,slack in zip(specs,pool.imap(check,specs)):
            print(*spec,slack,flush=True)
    print('The grouped middle signs cover 15/2 <= n/k <= 20.')
