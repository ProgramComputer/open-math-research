"""Exact finite-number-of-urn and binomial-tail mixtures at block weight one."""
import argparse, json, math, gzip
from flint import fmpz_poly as Z, fmpq_poly as Q

def variations(signs):
    return sum(x*y<0 for x,y in zip(signs,signs[1:]))

def signed_index(p,q):
    if not p:
        return 0
    p,q=Q(p),Q(q)
    if q.degree()>=p.degree(): q=q%p
    signs=[[],[]]
    while p:
        s=1 if p.leading_coefficient()>0 else -1
        signs[0].append(s*(-1)**p.degree())
        signs[1].append(s)
        p,q=q,-(p%q) if q else Q()
        if q:q=Q(q.numer())
    return variations(signs[0])-variations(signs[1])

def distinct(p):
    if p.degree()<1:return True
    sq=p//p.gcd(p.derivative())
    return signed_index(sq,sq.derivative())==sq.degree()

def orient(p,q):
    g=p.gcd(q)
    a,b=p//g,q//g
    if a.degree()<1:return b.degree()<=1
    if abs(a.degree()-b.degree())>1:return False
    return abs(signed_index(a,b))==a.degree() if a.degree()<=b.degree() else abs(signed_index(b,a))==b.degree()

def search(j,boxes,limit,ledger):
    from collections import Counter
    X=Z([0,1])
    a=[Z(0) for _ in range(limit+1)];a[0]=Z(1)
    cumul=a[:]
    counts=Counter(); failures={}
    def record(key,ok,box,n,P,R=None):
        counts[key]+=1
        if not ok and key not in failures:
            failures[key]=(box,n,[int(v) for v in P],None if R is None else [int(v) for v in R])
    for m in range(1,boxes+1):
        new=[]
        for n in range(limit+1):
            small=sum((a[n-i]*math.comb(n,i) for i in range(min(j,n+1))),Z(0))
            large=sum((a[n-i]*math.comb(n,i) for i in range(j,n+1)),Z(0))
            new.append(small+X*large)
        nxt=[2*c+w for c,w in zip(cumul,new)]
        for n,p in enumerate(new):
            assert p(1)==m**n
            record('urn real roots',distinct(p),m,n,p)
            record('truncation real roots',distinct(nxt[n]),m,n,nxt[n])
            if n:
                record('urn size interlace',orient(new[n-1],p),m,n-1,new[n-1],p)
                record('truncation size interlace',orient(nxt[n-1],nxt[n]),m,n-1,nxt[n-1],nxt[n])
            if m>1:
                record('last summand and prefix interlace',orient(cumul[n],p),m,n,cumul[n],p)
                record('successive prefixes interlace',orient(cumul[n],nxt[n]),m,n,cumul[n],nxt[n])
            ledger.write(json.dumps([j,m,n,[int(v) for v in p],[int(v) for v in nxt[n]]],separators=(',',':'))+'\n')
        a,cumul=new,nxt
    return {'j':j,'max_boxes':boxes,'max_n':limit,'counts':counts,'first_failures':failures}

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('boxes',type=int);ap.add_argument('n',type=int);ap.add_argument('j',type=int,nargs='+')
    ap.add_argument('--output',required=True);args=ap.parse_args()
    with gzip.open(args.output+'.jsonl.gz','wt') as ledger, open(args.output+'-summary.jsonl','w') as sm:
        for j in args.j:
            data=search(j,args.boxes,args.n,ledger)
            print(json.dumps(data),file=sm,flush=True)
            print(j,{key:val[:2] for key,val in data['first_failures'].items()},flush=True)
