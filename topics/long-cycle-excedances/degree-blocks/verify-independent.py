"""Independent rational replay of the joint value/derivative degree-bin slabs."""
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial, isqrt

GRID = 1 << 72
POLE_END = 99
POLES = tuple(range(-POLE_END, POLE_END+1, 2))
BINS_PER_BLOCK = 4
LOAD = Q(6,5)


def ceiling(numerator, denominator):
    return (numerator + denominator - 1)//denominator


def upward(value):
    scaled = value*GRID
    return ceiling(scaled.numerator, scaled.denominator)


def exp_lower(value):
    term = Q(1)
    result = term
    for j in range(1,65):
        term *= value/j
        result += term
    return result


def log_lower(value):
    u = (value-1)/(value+1)
    return 2*sum((u**(2*j+1)/(2*j+1) for j in range(18)), Q())


def log_upper(value):
    u = (value-1)/(value+1)
    return log_lower(value) + 2*u**37/(37*(1-u*u))


@lru_cache(None)
def kernel_box(c):
    positive = {
        p: upward((1+c*(p*p-1))**(-96))
        for p in range(1,POLE_END+1,2)
    }
    assert 191*c*POLE_END**2 > 1-c
    # Integral for both omitted tails, with lattice spacing two.
    weighted_tail = upward(1/(190*c*(1+c*(POLE_END**2-1))**95))
    zero_tail = ceiling(weighted_tail,POLE_END)
    return tuple(positive[abs(p)] for p in POLES), zero_tail, weighted_tail


@lru_cache(None)
def weighted_stars(c):
    terms, zero_tail, weighted_tail = kernel_box(c)
    star = [0,0]
    for a in range(1,POLE_END+3,2):
        plain = weighted = 0
        for index,p in enumerate(POLES):
            if p == a:
                continue
            gap = abs(p-a)
            plain += ceiling(terms[index],gap)
            weighted += ceiling(abs(p)*terms[index],gap)
        star[0] = max(plain,star[0])
        star[1] = max(weighted,star[1])
    return Q(star[0]+ceiling(zero_tail,2),GRID), Q(star[1]+ceiling(weighted_tail,2),GRID)


def pole_mass(c):
    terms,tail,_ = kernel_box(c)
    return Q(sum(terms)+tail,GRID)


def pole_diagonal(c,y_upper):
    terms,_,tail = kernel_box(c)
    finite = sum(term*max(1,y_upper*abs(p)) for p,term in zip(POLES,terms))
    return Q(finite+tail,GRID)


def pole_nonprincipal_first(c):
    terms,_,tail = kernel_box(c)
    return Q(sum(term*abs(p) for p,term in zip(POLES,terms) if abs(p)>1)+tail,GRID)


def bin_masses(k_min,aspect_hi):
    yield BINS_PER_BLOCK, Q(1), Q(1)
    for index in range(BINS_PER_BLOCK+1,BINS_PER_BLOCK*aspect_hi+1):
        block = (index-1)//BINS_PER_BLOCK
        left = Q(index-1,BINS_PER_BLOCK)
        right = Q(index,BINS_PER_BLOCK)
        if block == 1:
            bound = 1/(left-Q(1,k_min))-1/right
            if index == 2*BINS_PER_BLOCK:
                bound += Q(1,4*k_min)
        else:
            bound = (Q(1,BINS_PER_BLOCK)+Q(1,k_min))/(2*factorial(block))
        yield index,left,bound


def envelope_coefficients(k_min,aspect_lo,aspect_hi,A):
    max_bin = (BINS_PER_BLOCK+1)*aspect_hi
    degree = []
    for index, lo, weight in bin_masses(k_min,aspect_hi):
        plain, weighted = weighted_stars((lo-Q(1,k_min))*LOAD/(192*aspect_hi))
        normalized_power = Q(index,BINS_PER_BLOCK)/(aspect_lo*A)
        normalized_denominator = 1/(k_min*LOAD)
        degree.append((
            index,
            upward(weight*plain/A),
            upward(weight*(normalized_power*weighted+normalized_denominator*plain)),
        ))
    q = [GRID] + [0]*max_bin
    derivative = [0]*(max_bin+1)
    for cell in range(1,max_bin+1):
        power_count = angular_count = 0
        for bin_number, L, J in degree:
            if bin_number > cell:
                break
            power_count += bin_number*L*q[cell-bin_number]
            angular_count += J*q[cell-bin_number]
        q[cell] = ceiling(power_count,cell*GRID)
        derivative[cell] = ceiling(angular_count,GRID)
    q[0]=0
    return q,derivative


def estimate(min_n,aspect_lo,aspect_hi,minimum_A):
    B = BINS_PER_BLOCK
    k_min = min_n//aspect_hi
    assert k_min >= 1000
    q,derivative = envelope_coefficients(k_min,aspect_lo,aspect_hi,minimum_A)
    size_sqrt_lower = isqrt(k_min*aspect_lo)
    joint_value, joint_derivative, lag_correction = map(Q,(0,0,0))
    for b in range(B,len(q)):
        degree_lo = max(Q(1),Q(b,B+1))
        degree_hi = Q(b,B)
        if degree_lo > aspect_hi-1:
            continue
        min_old_y = max(Q(1,aspect_hi),1-degree_hi/aspect_lo)
        min_lag_y = max(Q(1,aspect_hi),1-(1+degree_hi)/aspect_lo)
        max_old_y = 1-degree_lo/aspect_hi
        old_weight = Q(4,7) if aspect_lo-degree_hi >= 2 else Q(1)
        lag_weight = Q(4,7) if aspect_lo-1-degree_hi >= 2 else Q(1)
        c = min_old_y*LOAD/192
        diag = pole_diagonal(c,max_old_y)
        offdiag = pole_nonprincipal_first(c/2)/size_sqrt_lower
        joint_value += Q(q[b],GRID)*old_weight*(diag+offdiag)
        joint_derivative += Q(derivative[b],GRID)*old_weight*pole_mass(c)
        lag_correction += Q(q[b],GRID)*lag_weight*pole_mass(min_lag_y*LOAD/192)
    lag_main = Q(4,7)*pole_mass((1-Q(1,aspect_lo))*LOAD/192)
    lag = pole_mass(LOAD/(192*aspect_hi))*(lag_main+lag_correction)/(aspect_lo*minimum_A)
    return Q(547,500)-Q(19,500)-joint_value-joint_derivative-lag


def run():
    assert log_upper(Q(7,4))+Q(1,1000)<Q(4,7)
    assert log_upper(Q(2))+Q(11,7000)<Q(5,7)
    assert Q(1,2)+(log_lower(Q(2))-Q(1,2))/4 > Q(547,1000)
    assert Q(3,2)+log_lower(Q(2))>4*Q(547,1000)
    assert (Q(4,7)**2)*(Q(1,50)**2+Q(1,16)**2) < Q(19,500)**2
    slabs = (
        (100000,4,6,10),(100000,6,10,10),(100000,10,16,10),
        (100000,16,25,10),(100000,25,34,9),(100000,34,42,8),
        (100000,42,50,Q(27,4)),(100000,50,62,7),(100000,62,75,7),
        (100000,75,86,Q(27,4)),(120000,86,96,7),
    )
    for n, lo, hi, a in slabs:
        a = Q(a)
        slack = estimate(n,lo,hi,a)
        assert slack>0
        if hi <= 50:
            assert (hi*a)**2<=n*LOAD
        else:
            assert (3*hi)**2<n*LOAD
            assert 25*a*a<=n//hi
        scaled = (slack*10**6).__floor__()
        print(f"{lo}..{hi}, n>={n}, A>={a}: lower margin {scaled}/10^6.")
    assert exp_lower(Q(117,10))>120000
    assert Q(89,100)*86>47+Q(5,2)*Q(117,10)
    assert exp_lower(Q(153,10))>4062720
    assert Q(89,100)*96>47+Q(5,2)*Q(153,10)
    print("All crossover comparisons pass.")


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit("Run without -O.")
    run()
