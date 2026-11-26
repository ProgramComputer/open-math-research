"""Certify strictly interlacing negative roots by reciprocal reduction and Arb signs."""
import argparse
from math import comb
from time import perf_counter

from flint import arb, arb_poly, ctx, fmpq, fmpq_poly, fmpz_poly


def eulerian_gamma(limit):
    out = [None, fmpz_poly([1])]
    for n in range(2, limit + 1):
        prev = out[-1]
        out.append(fmpz_poly([
            (j + 1) * prev[j] + (2 * (n - 2 * j) * prev[j - 1] if j else 0)
            for j in range((n + 1) // 2)
        ]))
    return out


class Signs:
    def __init__(self, gamma, size):
        self.coeffs = fmpz_poly([(-1)**j * c for j, c in enumerate(gamma)])
        self.prec = max(80, size * 2)
        ctx.prec = self.prec
        self.ball = arb_poly(self.coeffs)
        self.exact = None
        self.count = 0
        self.fallbacks = 0

    def at(self, x):
        self.count += 1
        if not x:
            return 1
        ctx.prec = self.prec
        val = self.ball(arb(x))
        if val > 0:
            return 1
        if val < 0:
            return -1
        self.fallbacks += 1
        if self.exact is None:
            self.exact = fmpq_poly(self.coeffs)
        val = self.exact(x)
        return (val > 0) - (val < 0)


def refine_one(old, endpoints, left):
    a, b = endpoints
    p = (a+b)/2
    s = old.at(p)
    if s == left:
        return p,b
    if s == -left:
        return a,p
    # p is an exact root. Preserve a strict bracket with complementary signs.
    return (a+p)/2,(p+b)/2


def transition(old, new, prev):
    m, mm = old.coeffs.degree(), new.coeffs.degree()
    if m not in (mm, mm-1) or len(prev) != m:
        raise ArithmeticError((m,mm,len(prev)))
    current = []
    lower = fmpq(0)
    expected = 1
    for endpoints in prev:
        for _ in range(2048):
            a,b = endpoints
            if new.at(a) == -expected and new.at(b) == -expected:
                break
            endpoints = refine_one(old, endpoints, expected)
        else:
            raise ArithmeticError("old and new brackets could not be separated")
        current.append((lower,a))
        lower = b
        expected = -expected
    if mm>m:
        upper = max(fmpq(1),2*lower)
        for _ in range(2048):
            if new.at(upper)==-expected:
                current.append((lower,upper))
                break
            upper *= 2
        else:
            raise ArithmeticError("no final bracket")
    return current


def certify(limit, selected_k, first_k, last_k):
    begin = perf_counter()
    cyc = eulerian_gamma(limit)
    counts = [0,0,0,0]
    t = fmpz_poly([0,1])
    for k in selected_k or range(first_k, min(last_k,limit//4)+1):
        rows = {}
        brackets = []
        started = perf_counter()
        generation = 0.0
        prior_counts = counts.copy()
        for n in range(k,limit+2):
            row_begin = perf_counter()
            gamma = cyc[n-1]
            for ell in range(k,n-k+1):
                gamma += comb(n-1,ell-1)*(t*cyc[ell-1]*rows[n-ell])
            if gamma.degree() != (n-2)//2 or gamma[0] != 1 or gamma[gamma.degree()]<=0:
                raise ArithmeticError((k,n,"degree/endpoint"))
            rows[n] = gamma
            generation += perf_counter()-row_begin
            new = Signs(gamma,n)
            if n==k:
                # Bootstrap a single-cycle row from size 3, already covered.
                old = Signs(cyc[2],3)
                for s in range(4,k+1):
                    new = Signs(cyc[s-1],s)
                    brackets = transition(old,new,brackets)
                    old = new
            else:
                brackets = transition(old,new,brackets)
                counts[0] += n-1>=4*k
                counts[1] += (n-3)*(n-1>=4*k)
                counts[2] += old.count
                counts[3] += old.fallbacks
            old = new
        counts[2]+=old.count
        counts[3]+=old.fallbacks
        delta = [a-b for a,b in zip(counts,prior_counts)]
        print(f"k={k:3d} old≤{limit} new_pairs={delta[0]} old_roots={delta[1]} "
              f"sign_calls={delta[2]} exact_fallback={delta[3]} "
              f"generation={generation:.3f}s elapsed={perf_counter()-started:.3f}s",flush=True)
    print(f"TOTAL {counts} in {perf_counter()-begin:.3f}s",flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("limit", type=int)
    parser.add_argument("--k", type=int, nargs="*")
    parser.add_argument("--first-k", type=int, default=4)
    parser.add_argument("--last-k", type=int, default=1_000_000)
    args = parser.parse_args()
    certify(args.limit,args.k,args.first_k,args.last_k)
