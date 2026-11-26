"""Independent slab and low-threshold boundary checks for the combined cutoff."""
from contextlib import redirect_stdout
from fractions import Fraction as Q
from io import StringIO
from math import ceil
from pathlib import Path
from runpy import run_path

HERE = Path(__file__).resolve().parent
with redirect_stdout(StringIO()):
    lattice=run_path(str(HERE/'verify_full_powers_independent.py'))['lattice']
    exp_bounds=run_path(str(HERE.parent/'review-radial-constants.py'))['exp_bounds']

TABLE = (
    (4,5,17,10000), (5,6,20,12000), (6,7,23,21601), (7,8,26,36054),
    (8,9,29,56768), (9,10,32,85334), (10,12,39,182520), (12,15,49,450188),
    (15,20,54,972000), (20,25,43,963021), (25,32,37,1168214),
    (32,40,30,1200000), (40,50,26,1408334), (50,64,24,1966080),
    (64,80,23,2821334), (80,96,23,4062720), (96,100,23,4408334),
    (100,125,24,7500000),
)

minimum=None
for low,cap,A,cutoff in TABLE:
    assert cutoff==max(10000,1000*cap,ceil(Q(5,6)*(cap*A)**2))
    W,W1,U,T,E,J=lattice(Q(999,160000*cap))
    a=Q(2,A)
    den=Q(1,low*A)
    ys=a*U
    es=ys/(1-ys)
    if cap<=15:
        assert ys<1
        tail2=ys*es/2
        R=a*T+W*tail2
        D=a*(E+den*T)+W1*tail2+a*(J+den*T)*es
        I=den*W*(W+R)
    else:
        V,V1,*_=lattice(Q(low-1,320*low))
        yl=Q(5,A)*U
        assert ys<yl<1
        el=yl/(1-yl)
        eps=1/exp_bounds(Q(low-1,8))[0]
        R=V*es+eps*W*el
        Ds=V1*es+den*(6*(V*W+V1*U)+ys*V)*(1+es)
        Dl=W1*el+den*(11*(W*W+W1*U)+yl*W)*(1+el)
        D=Ds+eps*Dl
        I=den*W*(V+R)
    slack=1-(R+Q(1,50))**2-(D+I+Q(1,16)+Q(1,100))**2
    assert slack>0
    if minimum is None or slack<minimum[0]:
        minimum=slack,low,cap
    print(f'{low}..{cap}, A={A}, row cutoff {cutoff}: squared slack > {int(slack*10**6)}/10^6')

pi_low,pi_high=Q(157,50),Q(22,7)
assert exp_bounds(Q(14))[0]>10**6 and 500>30*14+20
assert Q(1,2000)>Q(30,10**6)
assert exp_bounds(Q(1,5))[1]*66<82 and exp_bounds(Q(6))[0]>400
assert Q(3,20)-Q(3,20)**2/(2*11)>Q(148,1000)
assert Q(148*10**6,400000)>164+10+Q(3,2)*14
assert Q(148,400000)>Q(3,2*10**6) and exp_bounds(Q(10))[0]>18000
assert (81*11+pi_high**2)*(Q(2,5*11)+Q(1,25*11**2))<34<8*pi_low**2
assert Q(1,5)+pi_high**2/162<Q(262,1000)
assert 9**2*21>41**2 and 40*pi_low>11**2
peak=pi_high*exp_bounds(Q(262,1000))[1]
assert peak*(Q(1,41)+Q(1,11))<Q(12,25)
assert 9**2*11>29**2 and 81*20>4*19**2
assert peak/(exp_bounds(Q(29,8))[0]-1)<Q(12,25)
assert (1+Q(1,5*11))**2-1<Q(38,1000)
assert (1-Q(38,2000))/2>Q(49,100)
assert 4*10**6>81*399

assert min(cutoff for _,cap,_,cutoff in TABLE if cap==96)==4062720
for boundary,aspect,log_hi in ((4408334,96,Q(153,10)),(7500000,100,Q(16)),(250000**2,125,Q(25))):
    assert exp_bounds(log_hi)[0]>boundary
    assert Q(89,100)*aspect>47+Q(5,2)*log_hi
slack,low,cap=minimum
print(f'Least squared slack is >{int(slack*10**6)}/10^6 in {low}..{cap}.')
print('Small thresholds from one million and the combined cutoff of 4,062,720 pass.')
