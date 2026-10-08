#!/usr/bin/env python3
"""#915 actual physical VF late-owner inherited-prefix and half-scale probe.

NO prime-density substitution; every q below is a genuine sieved prime.
NO synthetic historical parent and NO newly available Co/Div compensation.

The exact Mobius dyadic formula retains original integer-site weights.
On the parity-reduced current square block its overlap has ZERO mass:
    paired_late(c) + paired_late(2c) = unpaired_outer_shell(c).

For a current odd composite n=c*q with q>R prime and q in the explicit
half-run [(R//2+1)^2,R^2), the ONLY possible odd cofactor >=3 is c=3.
Cofactors >=5 route to a prime owner before the half-run anchor, not to
another current or same-half-run site.
"""
import argparse
import math
from bisect import bisect_left, bisect_right


def sieve(N):
    prime = bytearray(b"\x01") * (N+1)
    prime[:2] = b"\x00\x00"
    small_factor = [0] * (N+1)
    for p in range(2, N+1):
        if prime[p]:
            if p*p <= N:
                for m in range(p*p, N+1, p):
                    prime[m] = 0
                    if not small_factor[m]:
                        small_factor[m] = p
    primes = [p for p in range(2,N+1) if prime[p]]
    return prime, primes, small_factor


def mobius(n, prime):
    if n==1: return 1
    sign = 1
    for p in range(2, math.isqrt(n)+1):
        if n % p == 0:
            n //= p
            if n%p == 0:return 0
            sign=-sign
            while n%p == 0:n//=p
    if n>1:sign=-sign
    return sign


def weight(R):
    return (2*R+1) / (R * math.log(R*R+R+.5))


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--extended",action="store_true")
    args=parser.parse_args()
    roots=[8,18,56,317,1027] + ([6000] if args.extended else [])
    limit=max((R+1)**2-1 for R in roots)
    prime, primes, sf=sieve(limit)
    for R in roots:
        X=(R+1)**2-1
        a=R//2+1
        b0=bisect_right(primes,R)
        w=weight(R)
        topThird=0
        sites=dict()
        squareful=0
        highOddComposite=0
        highOddCharge=0.
        largeCBeforeAnchor=0
        triplePairs=[]
        for n in range(R*R+1 if R%2==0 else R*R+2,X+1,2):
            if prime[n]:continue
            # Unique prime factor q>R (if any); all smaller factors are
            # inherited, possibly including squareful cofactors.
            m=n
            factors=[]
            while m>1:
                d=sf[m] or m
                factors.append(d)
                while m%d == 0:m//=d
            q=factors[-1]
            if q<=R:continue
            assert prime[q] and n%q==0
            c=n//q
            assert c>=3 and c%2 and c<q
            highOddComposite+=1
            highOddCharge+=w
            sites[c]=sites.get(c,0)+1
            if mobius(c,prime)==0:squareful+=1
            if q>=a*a:
                assert c==3, (R,n,c,q,a)
                qRoot=math.isqrt(q)
                historical_weight=weight(qRoot)-1
                assert a <= qRoot <R
                triplePairs.append((q,n,historical_weight,w,historical_weight+w))
            elif c>=5:
                largeCBeforeAnchor+=1
            if q>X//3:
                assert c==1, (R,n,c,q)
                topThird+=1
        assert topThird==0
        # Original anchored U,L and D: independent exact accounting of
        # scalar first-bad margin. This test does not prove its sign.
        D=bisect_right(primes,R*R)-sum(
            (2*r+1)/math.log(r*r+r+.5) for r in range(2,R))
        P=bisect_right(primes,X)-bisect_right(primes,R*R)
        U=max(-D,0)+w*(R-P)
        L=max(D,0)+(1-w)*P
        B=6*U*L-U*U-L*L
        assert abs((U-L)+(
            bisect_right(primes,X)-sum(
               (2*r+1)/math.log(r*r+r+.5) for r in range(2,R+1))
        ))<3e-4

        # Exact weighted dyadic packet on ORIGINAL site weights, including
        # c=1 prime seat, odd composites, squareful c (Mobius=0).
        for c in (1,3,5,7,9,15,21,31):
            if c>R:continue
            mu=mobius(c,prime)
            piEnd=bisect_right(primes,X//c)
            ownerqs=primes[b0:piEnd]
            direct=0.
            outer=0.
            overlap=0.
            for q in ownerqs:
                n=c*q
                wn=(w-int(bool(prime[n]))) if R*R<n<=X and n%2 else 0.
                direct+=mu*wn
                if 2*n<=X:
                    partner=0. # 2*n is even: physical parity weight zero
                    overlap+=mu*(wn-partner)
                    assert wn==0.,(R,c,q,n,wn)
                else:
                    outer+=mu*wn
            assert abs(direct-(outer+overlap))<1e-6,(R,c,direct,outer,overlap)
            assert abs(overlap)<1e-8
            if R in (18,317,1027) and c in (1,3,5,9):
                print("DYADIC R=%d c=%d mu=%d physical=%.6f overlap=%.6f unmatched=%.6f PASS"
                      %(R,c,mu,direct,overlap,outer))
        if R>=16:
            # For odd 3*q in the current square block, q lies in the
            # chronological explicit half run, which is NOT a Co/Div match.
            triple_q=[q for q in primes[
                  bisect_right(primes,R*R//3):
                  bisect_right(primes,X//3)]]
            assert len(triplePairs)==len(triple_q)
            assert all(sum(x[2:])<0 for x in triplePairs),(R,triplePairs[:3])
        pairTotal=sum(x[4] for x in triplePairs)
        sample=sorted(sites.items(),key=lambda kv:-kv[1])[:5]
        print("HISTORY R=%d half_a=%d highq_current_composites=%d "
              "squareful=%d cofactor_ge5_before_anchor=%d triples=%d "
              "sum_triple_real_degree_one=%.6f highq_charge=%.6f "
              "original_slack=%.6f topcofactors=%s PASS"
              %(R,a,highOddComposite,squareful,largeCBeforeAnchor,
                len(triplePairs),pairTotal,highOddCharge,B,sample))
        assert largeCBeforeAnchor<=highOddComposite
        # Quasi-RH/PNT are NOT invoked to infer a signed pair payment.
    print("PASS actual-prime inherited-prefix / dyadic physical overlap / half-scale bottleneck")
    print("OPEN: retain genuine cofactor ancestry inside original anchored CoDiv pair Fubini")


if __name__=="__main__":
    main()
