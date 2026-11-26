"""Compare central insertion ratios from labeled cycles and rational tangent coefficients."""
from fractions import Fraction as Q
from math import comb

LIMIT = 80


def cycle_values(limit):
    # At -1, record each cycle polynomial together with its first derivative.
    rows = []
    old = [1]
    for ell in range(1, limit + 1):
        if ell == 1:
            rows.append((0, 0))
        else:
            v = sum((-1)**j * a for j, a in enumerate(old))
            slope = sum((-1)**(j-1) * j * a for j, a in enumerate(old) if j)
            rows.append((-v, v-slope))
        new = [0] * ell
        for j, a in enumerate(old):
            new[j] += (j+1)*a
            if j+1 < ell:
                new[j+1] += (ell-1-j)*a
        old = new
    return [(0, 0)] + rows


def signed_rows(k, cycles):
    rows = [(1, 0)]
    for n in range(1, len(cycles)):
        value = derivative = 0
        for ell in range(k, n + 1):
            a, b = cycles[ell]
            x, y = rows[n-ell]
            weight = comb(n-1, ell-1)
            value += weight*a*x
            derivative += weight*(a*y+b*x)
        rows.append((value, derivative))
    return rows


def tangent_weights(limit):
    # If tan(z) = sum T_j z^(2j-1), the Riccati equation gives T_j.
    tangent = [Q(0), Q(1)]
    for j in range(2, limit + 1):
        tangent.append(sum(tangent[i]*tangent[j-i] for i in range(1, j))/(2*j-1))
    return [x/2 for x in tangent]


def check():
    cycles = cycle_values(LIMIT + 1)
    u = tangent_weights(LIMIT)
    count = 0
    top = Q(35, 68)
    for k in range(3, LIMIT + 1):
        rows = signed_rows(k, cycles)
        v = (k+1)//2
        coeff = [Q(1)]
        for m in range(1, (LIMIT+1)//2 + 1):
            coeff.append(sum((u[j]*coeff[m-j] for j in range(v, m+1)), Q(0))/m)
        for n in range(k, LIMIT + 1):
            value, slope = rows[n]
            if n % 2 == 0:
                if value == 0:
                    raise ArithmeticError(f"Missing even-row sign at {(n,k)}")
                continue
            if value != 0 or slope == 0:
                raise ArithmeticError(f"Wrong central multiplicity at {(n,k)}")
            lag = -comb(n,k-1)*cycles[k][0]*rows[n+1-k][0]
            actual = Q(lag, 2*slope)
            target = Q(0)
            if k % 2 == 0:
                N = (n+1)//2
                target = u[v]*coeff[N-v]/sum(u[j]*coeff[N-j] for j in range(v+1, N+1))
                threshold_max = u[v]**2/(v*u[2*v])
                if actual > threshold_max or (actual == threshold_max) != (n == 2*k-1):
                    raise ArithmeticError(f"Incorrect threshold maximum at {(n,k)}")
            if actual != target or not 0 <= actual <= top or (actual == top) != ((n,k) == (7,4)):
                raise ArithmeticError(f"Central ratio mismatch at {(n,k)}")
            count += 1
    if count != 1521:
        raise ArithmeticError("Incomplete exact check")
    print(f"Checked {count} central ratios through old size {LIMIT}. Unique global equality at (7,4).")


if __name__ == "__main__":
    check()
