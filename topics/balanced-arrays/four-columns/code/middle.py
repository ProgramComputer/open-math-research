"""Rigorous interval replay for the compact four-column saddle estimate."""
from fractions import Fraction
from flint import arb, ctx


def value(q):
    return arb(q.numerator) / q.denominator


def compact_bound(t):
    # n=533 maximizes each term in the displayed error majorant.
    n = 533
    root = arb(2).sqrt()
    pi = arb.pi()
    s2 = 1 + 4*root*t + 16*t**2 + 24*root*t**3 + 36*t**4
    real = (root*t + 8*t**2 + 14*root*t**3 + 24*t**4)/s2
    imag = (root*t + 4*t**2 + 2*root*t**3)/s2
    h = (real**2 + imag**2).sqrt()
    a0 = 37*real/50
    a = 3*(4*root*t/9 + 16*t**2/3 + 16*root*t**3/3 + 16*t**4)/(pi**2*s2)
    b = (2*root*t + 12*root*t**3)/s2
    B = (t/2+4*t**2/3)/s2.sqrt() + h**2/2
    K = 4*t/(3*arb(3).sqrt()*s2.sqrt())
    def pow32(x):
        return x * x.sqrt()
    local = arb(21)/20 * pow32(h/a0)/(n*a0) * (15*B/(4*a0)+105*(K/a0)**2/16)
    def tail(rate):
        x = n*rate/4
        return pow32(h/rate)*(x.sqrt().erfc()+2*(x/pi).sqrt()*(-x).exp())
    wrong = pow32(2*h/a)*(-n*b/4).exp()
    return local + tail(a) + tail(real) + wrong


def phase_join():
    # t_40 = y/(16n-shift); u = 1/n stays in [0,1/533].
    root = arb(2).sqrt()
    pi = arb.pi()
    y, shift = 718, 507
    for i in range(64):
        u = value(Fraction(i,64*533)).union(value(Fraction(i+1,64*533)))
        nt = y/(16-shift*u)
        t = nt*u
        h = (2*root+6*t)/(1+2*root*t)
        arg_ratio = (t*h)**2
        # atan(z)/z <= 1-z²/3+z⁴/5 for 0<=z<=1.
        slope = h*(1-arg_ratio/3+arg_ratio**2/5)
        theta = (t*h).atan()
        arg_lambda = pi/4 + (root*t/(1+root*t)).atan()-theta
        if not (nt>40 and t<arb(1)/5 and nt*slope-3*arg_lambda/2 < 41*pi):
            raise ArithmeticError(f"failed to join at cell {i}")
    return 64


if __name__ == "__main__":
    ctx.prec=128
    lo,hi=Fraction(1,5),Fraction(38,7)
    parts=2048
    worst=0
    for i in range(parts):
        t=value(lo+(hi-lo)*i/parts).union(value(lo+(hi-lo)*(i+1)/parts))
        error=compact_bound(t)
        if not error < arb(1)/2:
            raise ArithmeticError(f"cell {i} has unresolved bound {error}")
        worst=max(worst,int((100000*error).upper().ceil().unique_fmpz()))
    print(f"All {parts} compact intervals have error <= {worst}/100000.")
    print(f"Checked {phase_join()} reciprocal-row intervals for the phase join.")
