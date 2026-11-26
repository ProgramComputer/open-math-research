"""Exact scalar bounds for the two-step Fourier circle proof."""
from fractions import Fraction as Q


def exp_bounds(x):
    assert 0 <= x <= 128
    # Scaling keeps the Taylor remainder geometric with a small ratio.
    y = x/32
    term = low = Q(1)
    for j in range(1,37):
        term *= y/j
        low += term
    high = low + term*y/37/(1-y/38)
    # The independently rounded dyadic interval keeps later powers inexpensive.
    scale = 1 << 90
    lo_num = (scale*low).__floor__()
    hi_num = (scale*high).__ceil__()
    return Q(lo_num,scale)**32,Q(hi_num,scale)**32


def Elo(x):
    return exp_bounds(Q(x))[0]


def Ehi(x):
    return exp_bounds(Q(x))[1]


def log_upper(x):
    q=(x-1)/(x+1)
    partial = 2*sum((q**(2*j+1)/(2*j+1) for j in range(36)), Q())
    return partial+2*q**73/(73*(1-q*q))


pi_lo,pi_hi=Q(157,50),Q(22,7)
e_upper=Ehi(1)
assert e_upper<3


def small_contraction(k,beta,U,change,tail):
    # Compare G on the wider circle to L at contracted radius (1-1/k)r.
    assert beta**2/pi_lo**2+Q(1,k)<U**2
    assert Ehi(1)-1/Ehi(1)+Q(1,k-1)<change
    assert 1/(Elo(1)*(1-Q(1,2*k)))<tail
    return Q(12,k)+(change+1)*(2+Q(9,2)*U)+2*tail*(2+Q(9,4)*U)


def large_contraction(k,beta,shift,ratio,split,chernoff,outer_first,main_first,
                      outer_decay,main_decay,contracted_bound):
    assert pi_hi**2/(2*beta**2)<shift
    assert 1+shift/k<ratio
    wider_shift=shift+ratio
    assert 2*ratio*split*Ehi(wider_shift*split)<outer_first
    assert ratio*split*Ehi(shift*split)<main_first
    assert chernoff-wider_shift/k>outer_decay
    assert chernoff-shift/k>main_decay
    # A geometric sum costs at most the reciprocal of its exponent.
    radial_tail = 2*ratio/(k*outer_decay)+ratio/(k*main_decay)
    assert contracted_bound>2/(1-shift)
    return outer_first+main_first+radial_tail+2*contracted_bound


assert log_upper(Q(7,5)) < Q(337,1000)
assert 1-Q(5,7)*(1+log_upper(Q(7,5)))>Q(9,200)
assert Elo(Q(5))>100
assert Elo(Q(4))>50
assert Elo(Q(7,3))>10
assert 6/Elo(Q(100,6))<Q(1,10)
assert 5/Elo(Q(50,6))<Q(1,10)
assert Q(10,3)/Elo(Q(10,6))<1
# log 2 - 1/2 > 1/6, from two positive atanh-series terms.
assert 2*(Q(1,3)+Q(1,81))>Q(2,3)
assert 1-Q(1,2)*(1+log_upper(Q(2)))>Q(1,8)

assert small_contraction(100,4,Q(32,25),Q(237,100),Q(38,100))<30
assert large_contraction(100,4,Q(31,100),Q(1004,1000),Q(5,4),Q(1,50),
                         Q(27,2),Q(2),Q(1,146),Q(1,146),Q(31,10))<30
assert 1-Q(4,5)*(1+log_upper(Q(5,4)))>Q(1,50)
assert 2/Q(69,100)+Q(1,10)<Q(31,10)

assert small_contraction(50,4,Q(129,100),Q(238,100),Q(39,100))<32
assert large_contraction(50,4,Q(31,100),Q(1007,1000),Q(7,5),Q(9,200),
                         Q(18),Q(11,5),Q(1,54),Q(1,54),Q(31,10))<32
assert small_contraction(10,8,Q(257,100),Q(247,100),Q(39,100))<60
assert large_contraction(10,8,Q(78,1000),Q(1008,1000),Q(2),Q(1,8),
                         Q(36),Q(12,5),Q(1,61),Q(1,9),Q(16,5))<60
assert 2/Q(922,1000)+1<Q(16,5)

# Nonprincipal pole and phase bounds for k >= 100.
beta=Q(627,100)
assert pi_lo**2*(4-Q(1,100))>beta**2
assert 1+pi_hi**2/(2*beta**2)<Q(563,500)
assert (beta/2)**2/(2*(1+beta/20))>Q(37,10)
assert 2/Elo(Q(37,10))/(1-1/Elo(Q(37,5)))<Q(1,20)
assert (Q(21,20)*pi_hi*Ehi(Q(563,500))/Q(21,50))**2<2*pi_lo*99

# Nonprincipal comparison for 10 <= k <= 99.
assert pi_lo**2*(8/(2+Q(1,10))-Q(1,10))>36
assert 1+pi_hi**2/72<Q(57,50)
assert 36*10>18**2 and 2*pi_lo*9>7**2
assert 36*50>42**2 and 2*pi_lo*49>17**2
assert pi_hi*Ehi(Q(57,50))*(Q(1,18)+Q(1,7))<2
assert pi_hi*Ehi(Q(57,50))*(Q(1,42)+Q(1,17))<Q(82,100)
assert pi_hi*Ehi(Q(57,50))/(Elo(Q(25,4))-1)<Q(1,50)
assert 10000*pi_lo*pi_lo/(98**2+pi_lo*pi_lo)>10
assert 10000*pi_lo*pi_lo/(198**2+pi_lo*pi_lo)>Q(5,2)
assert Q(1,2)-Q(21,100)/4>Q(44,100)
assert Q(1,2)-Q(2,100)/4>Q(49,100)


def weighted_tail(decay,phase):
    a=decay-phase/4
    return 3/Elo(8*decay-4*phase)+(5+1/(4*a))/Elo(24*a)


assert weighted_tail(Q(49,100),Q(21,50))<Q(33,100)
assert weighted_tail(Q(44,100),Q(1,50))<Q(11,100)
assert weighted_tail(Q(44,10),Q(2))<Q(11,100)
assert weighted_tail(Q(11,10),Q(82,100))<Q(11,100)

# Finite-aspect Fourier region, 48 <= x <= 100.
square_shift=Q(48,25)
gap=Q(39,1000)
assert (2-square_shift)+2*gap<Q(16,100)
assert 2*gap<2-square_shift
assert square_shift/2-square_shift**2/400>Q(95,100)
assert 1+Q(2,100)<Q(101,100)**2
assert 1+8/(gap/4)<822
assert 1/(1+pi_hi)>Q(1,5)
assert (1-(pi_hi/100)**2/24)/Ehi(pi_hi/2)>Q(1,5)
assert gap*Q(507,100)**2>1
assert Q(99,1000)**2<Q(99,10000)
assert 2+2/Q(99,1000)<23
assert 2+2/Q(99,1000)+3/Q(99,10000)<326
assert 3*Q(507,100)*23<350
assert 3*Q(507,100)*326<4959
V0=350**2+Q(101,100)*3*23/gap
V1=350*4959+Q(101,100)*3*326/gap
assert V0<125_000
assert V1+(Q(69,100)*Q(48,46)+Q(1,100))*125_000<1_860_000
scale=Q(4110,2*48*47)/Elo(Q(95,100)*48-30)
assert 125_000*scale<Q(2,100)
assert 1_860_000*scale<Q(29,100)
assert 1-Q(13,100)**2>Q(62,100)**2

# Narrower 44 <= x <= 48 band with better moment and denominator constants.
assert Q(101,100)+Q(11,10)<Q(9,4)
assert Q(11,10)-Q(101,100)>gap/(Q(9,4)*100)
assert gap*4*Q(48,100)*pi_hi/9<Q(3,100)
assert Ehi(Q(1,5))*pi_hi<4
assert 1-1/Elo(Q(2,5))>Q(3,200)
assert 1+9/gap<232
assert 1/(1+Q(48,100)*pi_hi)>Q(1,3)
assert (1-(pi_hi/100)**2/24)/Ehi(Q(24,100)*pi_hi)>Q(1,3)
nu=Q(99,100*48)
assert Q(143,1000)**2<nu
assert 2+2/Q(143,1000)<16
assert Q(107,100)**2>Q(9,8)
assert 2+2*Q(107,100)/Q(143,1000)+Q(108,94)/nu<74
assert 3*Q(507,100)*16<244
assert 3*Q(507,100)*74<1126
assert 244**2+Q(101,100)*3*16/gap<61_000
assert (244*1126+Q(101,100)*3*74/gap
        +(Q(48,100)*Q(44,42)+Q(1,100))*61_000) < 313_000
scale_narrow=Q(696,2*44*43)/Elo(Q(95,100)*44-30)
assert 61_000*scale_narrow<Q(9,100)
assert 313_000*scale_narrow<Q(44,100)
assert 1-Q(1,5)**2>Q(77,100)**2

# Uniform large-aspect Fourier region, x >= 100 and k >= 100.
assert Q(9,400)+Q(1,40)<Q(1,5)  # total excluded lengths
assert Q(9,10)-Q(81,10000)>Q(89,100)
assert (Q(2,100)+pi_hi/100)*(32+Q(1,100))<2
assert Q(99,100)*Q(101,100)**2>1
assert Q(1,5)+Q(202,100)<3
assert Q(2,100)+Q(202,1000)+Q(100,33)<4
assert 81+Q(909,1000)<82
assert 108+Q(1212,1000)<110
assert 82*(Q(9,10)*Q(50,49)+Q(1,100))<77
assert 110+Q(77,10)<120
assert 120*Q(100,99)<122
assert Q(122*10**5)/Elo(Q(59))<Q(1,100)

# k below 100 with the direct Cauchy bound.
assert Q(9,10)-Q(81,100)/(2*50)>Q(89,100)
assert Q(9,10)-Q(81,100)/(2*10)>Q(85,100)
assert Elo(Q(10))>10_000
assert Q(89,100)*10000/99>45+25
assert Q(85,100)*10000/49>73+25
assert Q(218,1000)*10000/9>119+11+15
assert Elo(13)>130_000
print("All rational scalar bounds pass for n >= 10,000 and n/k >= 44.")
