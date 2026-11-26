"""Replay the tilted size comparison and signs at all missing geometric indices."""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
from runpy import run_path


HERE = Path(__file__).resolve().parent
PRIOR = HERE.parent / "dense-regime/below-cap/finite-aspect/marked-row"
MIXED = run_path(str(PRIOR / "mixed-phase/verify.py"))
N, D, R = 10**6, 250000, 127000
FIRST, SEVEN_LAST, LAST = 506471, 506800, 507905
WITNESSES = HERE / "finite-tilts.json"


def overlap_bound():
    assert FIRST-4 > (N-1)//2 and LAST <= 508000
    assert Q(51,50)**508 * Q(25,26)**260 < Q(9,10)
    epsilon = Q(1,10**20)
    assert D * Q(9,10)**1000 < epsilon
    tilt = (1+Q(1,260000)) * (1-epsilon)
    assert 1-1/tilt > Q(1,260100)


def deficit_lower(k):
    s = N*R-D*(k-1)
    rank = Q(R*(D-R),D)
    second = Q(s*(s-1), N*(N-1))
    error = min(second/rank + Q(s,N)/rank + Q(2*s,R*N),
                (2/rank+Q(2,R))*second)
    return Q((D-R)*N,D*(N-k+1))*Q(N-1,N+s-1)*(1-error)


def curvature_floor(k, z):
    loss = max(Q(0), deficit_lower(k))
    if k < 507300:
        loss = max(loss, MIXED["residual_lower"](N,k-1))
    mean = Q(N*R-D*k,N)*Q(N-k,N-k+1)
    return Q(4*D,N+2) + D*z*loss*mean


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--make-tilts", action="store_true")
    parser.add_argument("--exact-odds", action="store_true")
    args = parser.parse_args()
    indices = range(FIRST-3,SEVEN_LAST+3)
    if args.make_tilts:
        tilts = {str(k):MIXED["proposed"](N-1,k+1) for k in indices}
        WITNESSES.write_text(json.dumps(tilts,separators=(",",":"))+"\n")
        return
    if args.exact_odds:
        z = Q(4*N,(N+1)**2)
        for k in range(FIRST-2,LAST+1):
            for q in (k-1,k):
                assert Q(N,(q+1)*(N-q)) >= z
        print("Using exact marked-row odds from the hypergeometric identity.")
    else:
        overlap_bound()
        z = Q(1,260100)
    tilts = json.loads(WITNESSES.read_text())
    assert set(tilts) == {str(k) for k in indices}
    intervals = {k:MIXED["phase_bounds"](k,tilts[str(k)]) for k in indices}
    floors = {k:curvature_floor(k,z) for k in range(FIRST-2,LAST+1)}
    ceilings = {k:D*(Q(1,k)+Q(1,N-k)) + intervals[k][1]-intervals[k-1][0]
                for k in range(FIRST-2,SEVEN_LAST+3)}
    exp_minus = MIXED["exp_negative"]
    margins = []
    for k in range(FIRST,SEVEN_LAST+1):
        stencil = range(k-2,k+3)
        a = min(floors[i] for i in stencil)
        b = max(ceilings[i] for i in stencil)
        assert 0 < a <= b
        margin = 1-2*exp_minus(a/2)[1]+2*exp_minus(2*b)[0]-2*exp_minus(9*a/2)[1]
        assert margin > 0, k
        margins.append((margin,k))
    smallest, index = min(margins)
    print(f"{len(margins)} seven-term signs at {FIRST}..{SEVEN_LAST}.")
    print(f"Minimum certified sign margin at {index} exceeds {int(smallest*10**7)}/10^7.")
    log4_upper = Q(1386294362,10**9)
    assert exp_minus(log4_upper)[1] < Q(1,4)
    minimum, index = min((floors[k],k) for k in range(SEVEN_LAST+1,LAST+1))
    assert minimum > log4_upper
    print(f"{LAST-SEVEN_LAST} factor-four signs at {SEVEN_LAST+1}..{LAST}.")
    print(f"Minimum certified log curvature at {index} exceeds {int(minimum*10**7)}/10^7.")
    degree = N*R//D
    assert FIRST == 506470+1 and LAST == degree-95 and degree == 508000
    print("Joined to the reviewed signs through 506470 and from 507905 to degree minus one.")


if __name__ == "__main__":
    main()
