#!/usr/bin/env python3
"""Exact integer-by-integer prime-comb wheel and independent sextic Phi/NNS audit.
This does NOT identify Mobius integer seats with OpenAI Hecke ideal atoms.
"""
import math
import cmath

ROOTS = (317, 1027)
LIMIT = max(r*r-1 for r in ROOTS)
spf = [0]*(LIMIT+1)
mu = [0]*(LIMIT+1)
primes = []
mu[1] = 1
for n in range(2, LIMIT+1):
    if not spf[n]:
        spf[n] = n
        mu[n] = -1
        primes.append(n)
    for p in primes:
        m = n*p
        if m > LIMIT:
            break
        spf[m] = p
        if n % p == 0:
            mu[m] = 0
            break
        mu[m] = -mu[n]


def frame(X):
    sign = [-1]*(X+1)
    sign[0] = 0
    sign[1] = 1
    touched = bytearray(X+1)
    up, down = 1, X-1
    records = []
    low = None
    high_delta = 0
    seen = 0
    sampled = {2,3,5,7,11,13,17,19,31,127,313,317,1021,1031}
    for p in primes:
        if p > X//2:
            break
        seen += 1
        prev_up, prev_down = up, down
        prev_S = up-down
        first = killed = flipped = killed_old = flipped_old = 0
        pos_delta = neg_delta = 0
        actual_delta = 0
        k = X//p
        for c in range(2,k+1):
            n = p*c
            old = sign[n]
            if old == 0:
                continue
            if c % p == 0:
                killed += 1
                killed_old += old
                sign[n] = 0
                delta = -old
            elif touched[n]:
                flipped += 1
                flipped_old += old
                sign[n] = -old
                delta = -2*old
            else:
                first += 1
                touched[n] = 1
                continue
            if old == 1:
                up -= 1
            else:
                down -= 1
            if sign[n] == 1:
                up += 1
            elif sign[n] == -1:
                down += 1
            actual_delta += delta
            pos_delta += max(0, delta)
            neg_delta += max(0, -delta)
        assert actual_delta == -killed_old-2*flipped_old
        S = up-down
        assert S == prev_S+actual_delta
        co_cross = prev_up*pos_delta + prev_down*neg_delta
        div_cross = prev_up*neg_delta + prev_down*pos_delta
        assert co_cross-div_cross == prev_S*actual_delta
        diagonal = up+down
        co_same = up*(up-1)//2 + down*(down-1)//2
        div_opposite = up*down
        assert S*S == diagonal+2*(co_same-div_opposite)
        if p*p > X:
            assert killed == 0
            assert actual_delta == -2*sum(mu[2:k+1])
            high_delta += actual_delta
        if p <= math.isqrt(X):
            low = S
        if p in sampled or (p <= math.isqrt(X) and seen < len(primes)
                             and primes[seen] > math.isqrt(X)):
            records.append((p,first,killed,flipped,actual_delta,S,diagonal,
                            co_same-div_opposite,co_cross-div_cross))
    assert sign[1:] == mu[1:X+1]
    M = sum(mu[1:X+1])
    assert up-down == M
    assert M == {317:-28,1027:367}[int(math.isqrt(X+1))]
    assert low + high_delta == M
    final_K = up+down
    final_pair = up*(up-1)//2+down*(down-1)//2-up*down
    assert M*M == final_K+2*final_pair
    return dict(X=X,root=math.isqrt(X+1),M=M,low=low,high_delta=high_delta,
                primes_processed=seen,final_K=final_K,final_CoDiv=final_pair,
                records=records)


def frozen_first_hit(X):
    """The frozen Boolean-face universe differs from the animation seed."""
    old=[(1,1)]
    F=1
    records=[]
    for p in primes[:11]:
        reachable=sum(sign for n,sign in old if n!=1 and p*n<=X)
        first_hit=-int(p<=X)
        new=old+[(p*n,-sign) for n,sign in old]
        newF=sum(sign for n,sign in new if n<=X)
        assert newF == F-reachable+first_hit
        records.append((p,F,reachable,first_hit,newF))
        old,F=new,newF
    return records


def phi(z):
    return (z.real-z.imag,z.real+z.imag)

def co_div_phase(atoms):
    fx=[phi(z)[0] for z in atoms]
    fy=[phi(z)[1] for z in atoms]
    upx=sum(max(x,0.) for x in fx)
    lox=sum(max(-x,0.) for x in fx)
    upy=sum(max(y,0.) for y in fy)
    loy=sum(max(-y,0.) for y in fy)
    co=(upx**2+lox**2+upy**2+loy**2)/2
    div=upx*lox+upy*loy
    diag=sum(abs(z)**2 for z in atoms)
    E=abs(sum(atoms))**2
    assert math.isclose(co-div,E,abs_tol=1e-9)
    assert diag<=co+1e-8
    return (diag,co-diag,div,E)


def phase_audit():
    # These are genuine finite ideal-labelled RHLean witnesses, NOT all OAI rows.
    witness={"x317":(5,5,1,1),"x1027":(1,3,3,5),
             "R317":(0,4,2,0),"R1027":(3,1,5,3)}
    roots=[cmath.exp(1j*math.pi*e/3) for e in range(6)]
    rows=[]
    for key,exps in witness.items():
        z=[roots[e] for e in exps]
        K,co,di,E=co_div_phase(z)
        assert round(E) in (1,4)
        rows.append((key,K,co,di,E))
    for theta in roots:
        A=1+0j
        B=theta
        x,y=phi(A)
        bx,by=phi(B)
        diag=abs(A)**2+abs(B)**2
        dot=(x*bx+y*by)/2
        assert math.isclose(abs(A-B)**2,diag-2*dot,abs_tol=1e-10)
    assert math.isclose(sum(v[-1]**2 for v in rows),19,abs_tol=1e-8)
    return rows


if __name__ == '__main__':
    for R in ROOTS:
        d=frame(R*R-1)
        print(f"SQUARE ROOT {R}, X={d['X']}: M(X)={d['M']}, "
              f"low-wheel S={d['low']}, high-prime delta={d['high_delta']}; "
              f"prime stages={d['primes_processed']}, K={d['final_K']}, "
              f"pair Co-Div={d['final_CoDiv']}")
        print('p | first-hit | square-kill | flip | delta-S | S | K | Co-Div | cross Co-Div')
        for row in d['records']:
            print(' | '.join(map(str,row)))
        p=next(p for p in primes if p > math.isqrt(d['X']))
        k=d['X']//p
        parent=sum(mu[1:k+1])
        print(f'First high prime p={p}: k=floor(X/p)={k}, M(k)={parent}, '
              f'wheel delta={-2*(parent-1)}')
        print('Frozen subset faces: p, F_old, reachable_parent, firsthit, F_new')
        for row in frozen_first_hit(d['X']):
            print(' | '.join(map(str,row)))
        print()
    print('Actual RH_Lean finite ideal-phase witnesses (separate from integer wheel)')
    print('row | diagonal | positive-offCo | divergent | row-energy')
    for row in phase_audit():
        print(' | '.join(f'{x:.6f}' if isinstance(x,float) else str(x) for x in row))
    print('PASS every integer, every sequential prime stage, original square root endpoint,'
          ' Boolean first-hit boundary and finite Hecke Phi/CoDiv; no analytic power claim')
