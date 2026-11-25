"""Check every numerical bound used at the beginning of the infinite nearest-pair tail."""
from fractions import Fraction as Q


def verify():
    n = 256
    N = n+1
    delta1 = 4*Q(1,8)**N + Q(n+3,2)*Q(7,10)**N
    delta2 = 4*Q(1,5)**N + 2*(n+1)*Q(4,5)**N
    def tail(j, v):
        t = 2*v**N
        if t >= 1:
            raise ArithmeticError("Geometric tail does not converge")
        return 2**j * (t/(1-t)**2 + (j+1)*t/(1-t))
    bounds = [2*delta1 + tail(1,Q(9,10)), Q(9,10)**N + 2*delta1 + 4*delta2 + tail(2,Q(24,25))]
    if max(bounds) >= Q(1,32) or 17*Q(9,10)**N >= 15*Q(2,3):
        raise ArithmeticError("Required base-index inequality failed")
    if not (3**5 < 2**8 and 2*Q(7,10)**2/Q(109,100) < Q(9,10)):
        raise ArithmeticError("Rational logarithm comparison failed")
    if 2*sum(Q(1,2)**(2*j+1)/(2*j+1) for j in range(3)) <= Q(109,100):
        raise ArithmeticError("Lower bound on log(3) failed")
    return bounds


if __name__ == '__main__':
    verify()
    print("Both uniform approximation errors are below 1/32, starting at n=256.")
