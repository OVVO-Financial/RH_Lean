#!/usr/bin/env python3
"""#915 exact unmatched discrete-Li transport versus ACTUAL moving-owner census.

Reproduces, by INDEPENDENT integer prime events and actual floor-Li jumps,
the positive/negative event populations on [(floor(R/2)+1)^2,(R+1)^2],
their once-paired cancellation, remaining unmatched signed boundary,
fixed-17 wheel removals, exact signed VF historical forcing, and ORIGINAL
(one-number anchor) NNS mass. No prime-density substitution.

The apparent matched count is an algebraic bijection count, NOT a claim
that every match has birth before death or finite transport lifetime.
"""
import math
from bisect import bisect_right
from functools import lru_cache

EULER_GAMMA = 0.577215664901532860606512090082402431
ZLOG2 = math.log(2.)
Q17 = 2*3*5*7*11*13*17


@lru_cache(maxsize=150_000)
def ei_pos(z: float) -> float:
    """Ei(z)=gamma+log(z)+sum_(k>=1) z^k/(k k!) for z>0."""
    term = z
    s = term
    for k in range(2, 160):
        term *= z/k
        add = term/k
        s += add
        if abs(add) < max(1., abs(s)) * 1.e-15:
            break
    return EULER_GAMMA + math.log(z) + s


EI_LOG2 = ei_pos(ZLOG2)


def li2(n):
    if n <= 2:
        return 0.
    return ei_pos(math.log(n)) - EI_LOG2


def li_floor(n):
    x=li2(n)
    assert abs(x-round(x))>2e-8, ("near floor integer; verify high precision",n,x)
    return math.floor(x)


def prime_sieve(N):
    arr=bytearray(b'\x01')*(N+1)
    arr[:2]=b'\x00\x00'
    for p in range(2,math.isqrt(N)+1):
        if arr[p]:
            arr[p*p:N+1:p]=b'\x00'*((N-p*p)//p+1)
    primes=[n for n in range(2,N+1) if arr[n]]
    return arr,primes


def midpoint_vf(R):
    return math.fsum((2*r+1)/math.log(r*r+r+.5) for r in range(2,R))


def block_weight(R):
    return (2*R+1)/(R*math.log(R*R+R+.5))


def run(R,prime,primes):
    a=R//2+1
    A,B=a*a,(R+1)**2
    primeA=bisect_right(primes,A)
    primeB=bisect_right(primes,B)
    act=primeB-primeA
    QA,QB=li_floor(A),li_floor(B)
    floor_count=QB-QA
    # The genuine q events where BOTH pi and floor-Li jump.
    common=0
    for n in primes[primeA:primeB]:
        assert n>4
        # By Li singleton increment <1 this test is a correct event atom.
        if li_floor(n)>li_floor(n-1):
            common+=1
    plus,minus=act-common,floor_count-common
    matched=min(plus,minus)
    rem_pos,rem_neg=plus-matched,minus-matched
    assert rem_pos>=0 and rem_neg>=0 and rem_pos*rem_neg==0
    EA=primeA-QA
    EB=primeB-QB
    assert rem_pos-rem_neg==act-floor_count==EB-EA
    actual_moving=required_moving=totalWheel=0
    for r in range(a,R+1):
        X=(r+1)**2
        wheel=sum(math.gcd(n,Q17)==1 for n in range((r*r+1)|1,X,2))
        P=bisect_right(primes,X)-bisect_right(primes,r*r)
        F=li_floor(X)-li_floor(r*r)
        actual_moving+=wheel-P
        required_moving+=wheel-F
        totalWheel+=wheel
    assert actual_moving-required_moving==minus-plus
    DA=primeA-midpoint_vf(a)
    DB=primeB-midpoint_vf(R+1)
    bridgeA=QA-midpoint_vf(a)
    bridgeB=QB-midpoint_vf(R+1)
    assert abs(DA-(EA+bridgeA))<2e-8
    assert abs(DB-(EB+bridgeB))<2e-8
    assert abs(DB-(DA+(rem_pos-rem_neg)+(bridgeB-bridgeA)))<2e-8
    blockP=bisect_right(primes,B)-bisect_right(primes,R*R)
    w=block_weight(R)
    DR=bisect_right(primes,R*R)-midpoint_vf(R)
    M=abs(DR)+(R-blockP)*w+blockP*(1-w)
    slack=M*M-2*DB*DB
    assert M>0
    print(
      "TRANSPORT R=%d a=%d actualPrime=%d floorLiEvents=%d "
      "coincident=%d rawPlus=%d rawMinus=%d matched=%d "
      "unmatchedPlus=%d unmatchedMinus=%d E_a=%d E_B=%d "
      "movingActual=%d movingLiDemand=%d ownerExcess=%+d "
      "D_a=%.9f D_B=%.9f bridgeDelta=%.9f "
      "originalM=%.9f originalSlack=%.9f PASS" %
      (R,a,act,floor_count,common,plus,minus,matched,rem_pos,rem_neg,
       EA,EB,actual_moving,required_moving,
       actual_moving-required_moving,DA,DB,bridgeB-bridgeA,M,slack)
    )
    return rem_pos,rem_neg,common


def main():
    import argparse
    ap=argparse.ArgumentParser()
    ap.add_argument('--extended',action='store_true')
    args=ap.parse_args()
    roots=(8,18,56,317,1027,2000) if args.extended else (18,317,1027)
    arr,primes=prime_sieve((max(roots)+1)**2)
    for R in roots:
        run(R,arr,primes)
    print("PASS actual-prime vs floor-Li once-canceled boundary and original anchored VF mass")
    print("OPEN all-scale duration/active-interval bound or genuine first-bad paid arithmetic")


if __name__ == '__main__':
    main()
