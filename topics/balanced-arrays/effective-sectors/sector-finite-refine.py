"""Sharper exact intervals at the minimum cap for binary64 sweep misses."""
import argparse
from collections import Counter
from fractions import Fraction as F
from math import comb, isqrt
from pathlib import Path
from runpy import run_path
import sys


class Probability:
    def __init__(self, n, d, r, k, joint):
        self.joint = joint
        self.parameters = n,d,r,k
        self.total = comb(n,k)**d
        self.lower = 0
        self.upper = self.total
        self.partial = self.total
        self.order = 0
        self.bound = min(n,k*d//(r+1))
        self.done = False
        row_tail = F(sum(comb(d,i)*k**i*(n-k)**(d-i) for i in range(r+1,d+1)),n**d)
        self.na = (1-row_tail)**n

    def advance(self, order):
        if not self.done:
            n,d,r,k = self.parameters
            for h in range(self.order+1,min(order,self.bound)+1):
                term = comb(n,h)*self.joint(n,d,r,k,h)
                self.partial += (-1)**h*term
                if h%2:
                    self.lower = max(self.lower,self.partial)
                else:
                    self.upper = min(self.upper,self.partial)
                self.order = h
                if h == self.bound or not term:
                    self.lower = self.upper = self.partial
                    self.done = True
                    break
        upper = F(self.upper,self.total)
        return F(self.lower,self.total), upper if self.done else min(upper,self.na)


def check(n,d,r,problematic,order_limit,joint):
    needed = {k+i for k in problematic for i in range(-3,4)}
    prob = {k: Probability(n,d,r,k,joint) for k in needed}
    unresolved = problematic[:]
    for order in (1,3,5,8,12,16,24,32,48):
        if order>order_limit:
            break
        needed = {k+i for k in unresolved for i in range(-3,4)}
        bands = {k: prob[k].advance(order) for k in needed}
        def curvature(k):
            mid = F((k+1)*(n-k+1),k*(n-k))**d
            l1,u1 = bands[k-1]
            l2,u2 = bands[k]
            l3,u3 = bands[k+1]
            return max(mid,mid*l2**2/(u1*u3)), mid*u2**2/(l1*l3) if l1*l3 else None
        out = []
        for k in unresolved:
            lo = [curvature(k+i)[0] for i in range(-2,3)]
            if lo[2]>4:
                continue
            interval = 2**32
            T = F(isqrt(interval**2*lo[2].denominator//lo[2].numerator)+1,interval)
            C = F(0)
            for sign in (-1,1):
                upper = curvature(k+sign)[1]
                if upper:
                    C += (1-T/(lo[2+sign]*lo[2+2*sign]))/upper
            result = 1-2*T+C*T*T if C*T<=1 else 1-1/C
            if result<=0:
                out.append(k)
        unresolved = out
        if not unresolved:
            return order, []
    return order, unresolved


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("misses", type=Path)
    parser.add_argument("--counter", required=True, type=Path)
    args = parser.parse_args()
    joint = run_path(str(args.counter))["joint_overload"]
    hist = Counter()
    for line in args.misses.read_text().splitlines():
        n,d,r,_,start,end = map(int,line.split())
        order,left = check(n,d,r,list(range(start,end+1)),8,joint)
        if left:
            raise ArithmeticError((n, d, r, left))
        hist[order] += 1
        print(n,d,r,order,','.join(map(str,left)) if left else 'covered',flush=True)
    print(hist,file=sys.stderr)
