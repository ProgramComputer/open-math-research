"""Exact centered-recursion certificate for the million-row balanced arrays."""
from fractions import Fraction as Q
from functools import lru_cache
import argparse

N, D, R = 1_000_000, 250_000, 127_000
UNIT, PGRID, EGRID = 2**88, 2**50, 2**60
BLOCKS = (
    (506471, 506570, 20),
    (506571, 506650, 15),
    (506651, 506750, 15),
    (506751, 506850, 15),
    (506851, 506950, 15),
    (506951, 507050, 15),
    (507051, 507075, 12),
    (507076, 507100, 12),
    (507101, 507125, 12),
    (507126, 507150, 12),
    (507151, 507175, 16),
    (507176, 507200, 16),
    (507201, 507225, 16),
    (507226, 507250, 20),
    *((a, a+4, 24) for a in range(507251,507301,5)),
)


def ceil_div(a, b):
    return (a+b-1)//b


def grid(value, unit, upper=False):
    a, b = value.numerator*unit, value.denominator
    return ceil_div(a,b) if upper else a//b


def coarse_up(value):
    return Q(grid(value, EGRID, True), EGRID)


@lru_cache(maxsize=4096)
def atom(m, z):
    """Outward bounds for the cap mass at exact probability z."""
    a, b = z.denominator-z.numerator, z.numerator
    lo = hi = tot_lo = tot_hi = UNIT
    for x in range(R):
        u, v = (R-x)*a, (m-R+x+1)*b
        lo = lo*u//v
        hi = ceil_div(hi*u,v)
        tot_lo += lo
        tot_hi += hi
        if u<v and hi <= 1<<20:
            tot_hi += ceil_div(hi*u,v-u)
            break
    return Q(UNIT,tot_hi), Q(UNIT,tot_lo)


@lru_cache(maxsize=512)
def matched(p):
    """Exact dyadic bisection with independent signs at both endpoints."""
    assert Q(1,2) < p < Q(R,D)
    left, right = grid(p,PGRID), grid(p+Q(1,100),PGRID,True)
    assert right < PGRID
    # The initial upper endpoint is independently checked, even if never used.
    def mean_bounds(z):
        ql, qh = atom(D,z)
        return D*z-z*(D-R)*qh, D*z-z*(D-R)*ql

    assert mean_bounds(Q(right,PGRID))[0] >= D*p
    while right-left > 4:
        mid = (left+right)//2
        lo, hi = mean_bounds(Q(mid,PGRID))
        if lo >= D*p:
            right = mid
        elif hi <= D*p:
            left = mid
        else:
            break
    zlo, zhi = Q(left,PGRID), Q(right,PGRID)
    assert zhi-zlo < Q(1,10**10)
    assert mean_bounds(zlo)[1] <= D*p <= mean_bounds(zhi)[0]
    return zlo,zhi


def terminal_lower(n, k):
    loss = Q(0)
    for j in range(7,-1,-1):
        height, quota = n-j, k-j
        assert 0<quota<height and D*(quota+1)<=height*R
        p = Q(quota,height)
        z = p/(1-(1-p)*loss)
        low = atom(D,z)[0]*Q(D-R,D)/(1-p)
        loss = Q(grid(low,EGRID),EGRID)
    return loss


def derivative(plo, phi):
    """Lower and upper bounds on the derivative of the matched log factor."""
    zlo = matched(plo)[0]
    zhi = matched(phi)[1]
    blo = (zlo-plo)*(R-(D-1)*phi)
    bhi = (zhi-phi)*(R-(D-1)*plo)
    vlo, vhi = phi*(1-phi), plo*(1-plo)
    assert 0<blo<=bhi<vlo
    return blo/(vhi*(vhi-blo)), bhi/(vlo*(vlo-bhi))


def deficit_bounds(z, a, b):
    """Upper bounds for E X, E X^2, E exp(a X+b X^2), X=r-J."""
    assert a>=0 and b>=0
    a, b = grid(a,EGRID,True), grid(b,EGRID,True)
    amin, bmin = z.denominator-z.numerator, z.numerator
    remaining = EGRID-a-b*(2*R+1)
    assert remaining>0
    lo = hi = tilted = total_lo = weighted = UNIT
    mom1 = mom2 = 0
    for i in range(R):
        u, v = (R-i)*amin, (D-R+i)*bmin
        lo = lo*u//v
        hi = ceil_div(hi*u,v)
        tilted = ceil_div(tilted*u*EGRID,v*(EGRID-a-b*(2*i+1)))
        total_lo += lo
        weighted += tilted
        mom1 += (i+1)*hi
        mom2 += (i+1)**2*hi
        # Use the largest exponential step factor on the entire remaining
        # support together with the current (largest) binomial step ratio.
        if u*EGRID < v*remaining and tilted <= 1<<20:
            tail_ratio_n, tail_ratio_d = u*EGRID, v*remaining
            weighted += ceil_div(tilted*tail_ratio_n,tail_ratio_d-tail_ratio_n)
            tail = ceil_div(hi*u,v-u)
            mom1 += R*tail
            mom2 += R*R*tail
            break
    return Q(mom1,total_lo), Q(mom2,total_lo), Q(weighted,total_lo)


def enclose(first, last, depth):
    """Uniform error for initial nearly balanced phases first through last."""
    k_min, k_max = first, last+1
    assert 0<k_min-depth-8 and k_max+1<N-depth-8
    assert D*(k_max+1)<=(N-depth-8)*R
    pmin,pmax = Q(k_min-depth,N), Q(k_max,N-depth)
    assert Q(1,2)<pmin<=pmax<Q(R,D)
    zmin,zmax = matched(pmin)[0], matched(pmax)[1]
    qmax = atom(D-1,zmax)[1]
    M = derivative(pmin,pmax)[1]
    tmax = R-D*pmin
    lower = terminal_lower(N-depth,k_min-depth)
    assert 0<=lower<=qmax<1
    error = coarse_up((qmax-lower)/(1-qmax))
    errors = [error]
    wmin = pmin/(1-pmin)
    for j in range(depth-1,-1,-1):
        height = N-j
        spread = Q(j+1,height)
        wd = spread/(1-pmax)**2
        assert 2*error<1
        swap = (1+wd/wmin)/(1-2*error)
        raw = wd*(swap-1)+spread**2/(1-pmax)**3+wd/(D-1)
        assert raw<wmin
        epsilon = raw/(wmin-raw)
        b = M/(D*(height-1))
        a = error+epsilon+b*(tmax+1)
        m1,m2,mgf = deficit_bounds(zmin,a,b)
        moment = a*m1+b*m2
        assert 0<=moment<1-qmax and mgf>=1
        gain = qmax*moment/(1-moment-qmax)
        loss = qmax*(1-1/mgf)/(1-qmax)
        error = coarse_up(max(gain,loss))
        errors.append(error)
    return error,errors


def log_curvature_bounds(k):
    a,b = Q(1,k),Q(1,N-k)
    return D*(a+b-(a*a+b*b)/2),D*(a+b)


def exp_bounds(x):
    assert 0<=x<10
    term = total = Q(1)
    for j in range(1,31):
        term *= x/j
        total += term
    return total,total+term*(x/31)/(1-x/32)


def certify(k, error):
    model_floor = Q(D,N)*derivative(Q(k-1,N),Q(k+1,N))[0]
    curvature = log_curvature_bounds(k)[0]+model_floor-2*D*error
    assert exp_bounds(Q(1_386_294_362,10**9))[0]>4
    if curvature>Q(1_386_294_362,10**9):
        return 'factor four',curvature

    # Optional seven-term gate. Every local curvature is within these
    # bounds, so the magnitudes at |j|<=3 lie in [exp(-hi*j²/2),exp(-lo*j²/2)].
    plo,phi = Q(k-3,N),Q(k+3,N)
    mlo,mhi = derivative(plo,phi)
    a = Q(D,N)*mlo-2*D*error
    b = Q(D,N)*mhi+2*D*error
    lo = a+min(log_curvature_bounds(i)[0] for i in range(k-2,k+3))
    hi = b+max(log_curvature_bounds(i)[1] for i in range(k-2,k+3))
    assert lo>0 and 0<hi<2
    margin = 1-2/exp_bounds(lo/2)[0]+2/exp_bounds(2*hi)[1]-2/exp_bounds(9*lo/2)[0]
    assert margin>0,(k,grid(margin,10**9))
    return 'seven terms',margin


def certify_block(first, last, depth, show_steps=False):
    # Include all phases used by both gates.
    error,errors = enclose(first-3,last+2,depth)
    results = {}
    for k in range(first,last+1):
        method,score = certify(k,error)
        if method not in results:
            results[method] = 0,score
        count,minimum = results[method]
        results[method] = count+1,min(minimum,score)
    print(f'{first}..{last}, depth {depth}, E <= {grid(error,10**12,True)}/10^12.')
    if show_steps:
        print('Error upper bounds from terminal to initial, on a 10^12 grid:')
        print(' '.join(str(grid(e,10**12,True)) for e in errors))
    for method,(count,minimum) in results.items():
        what = 'log-curvature' if method == 'factor four' else 'parity'
        print(f'  {method}: {count}; {what} exceeds {grid(minimum,10**9)}/10^9.')
    return {method: tally[0] for method,tally in results.items()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--first',type=int,default=507000)
    parser.add_argument('--last',type=int,default=507000)
    parser.add_argument('--depth',type=int,default=15)
    parser.add_argument('--transition',action='store_true')
    args = parser.parse_args()
    if args.transition:
        cursor = 506471
        counts = {'factor four': 0, 'seven terms': 0}
        for first,last,depth in BLOCKS:
            assert first == cursor and first<=last
            for method,count in certify_block(first,last,depth).items():
                counts[method] += count
            cursor = last+1
        assert cursor == 507301 and sum(counts.values()) == 830
        print(f'830 consecutive quotas certified: {counts}.')
    else:
        assert args.first<=args.last
        certify_block(args.first,args.last,args.depth,True)


if __name__ == '__main__':
    main()
