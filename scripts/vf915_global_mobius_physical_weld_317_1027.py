#!/usr/bin/env python3
"""Original 317/1027 VF site-by-site Mobius decoder and anchored NNS audit.

This independently constructs the original ODD OPEN square-block carrier;
the first square endpoint R^2 is excluded and the next square endpoint
(R+1)^2 is excluded. DO NOT reuse closed or cumulative Mertens carriers here.

No external packages and no analytic assumptions.
"""
from __future__ import annotations
import math

ROOTS = (317, 1027)
N = (max(ROOTS) + 1) ** 2
least_prime = [0] * (N+1)
mu = [0] * (N+1)
primes = []
mu[1] = 1
for n in range(2,N+1):
    if not least_prime[n]:
        least_prime[n] = n
        mu[n] = -1
        primes.append(n)
    for p in primes:
        m = n*p
        if m>N:
            break
        least_prime[m] = p
        if n%p==0:
            mu[m]=0
            break
        mu[m]=-mu[n]

pi=[0]*(N+1)
for n in range(1,N+1):
    pi[n]=pi[n-1]+int(n>1 and least_prime[n]==n)

vf_finished=0.
defect={}
for R in range(2,max(ROOTS)+2):
    defect[R]=pi[R*R]-vf_finished
    vf_finished+=(2*R+1)/math.log(R*R+R+.5)

for R in ROOTS:
    weight=(2*R+1)/(R*math.log(R*R+R+.5))
    counts=dict(primes=0,high_composites=0,smooth_composites=0,
                mu_pos_comp=0,mu_neg_comp=0,squareful=0)
    signed=0.
    absolute=0.
    mobius_square=0
    mobius_signed=0
    negative_depth=0
    high_source_mu=0
    high_source_correction=0.
    physical_high=0.
    physical_smooth=0.

    seats=[n for n in range(R*R+1,(R+1)*(R+1)) if n%2]
    assert len(seats)==R

    for n in seats:
        m=mu[n]
        is_prime=(least_prime[n]==n)
        odd_composite=int((not is_prime) and m==-1)
        decoder=weight-(m*m-m-2*odd_composite)/2
        actual=weight-int(is_prime)
        assert abs(decoder-actual)<1e-13,(R,n,m,decoder,actual)

        mobius_square+=m*m
        mobius_signed+=m
        negative_depth+=odd_composite
        signed+=actual
        absolute+=abs(actual)

        if is_prime:
            counts["primes"]+=1
        elif m==1:
            counts["mu_pos_comp"]+=1
        elif m==-1:
            counts["mu_neg_comp"]+=1
        else:
            counts["squareful"]+=1

        fac=n
        largest_prime=1
        while fac>1:
            q=least_prime[fac]
            largest_prime=max(largest_prime,q)
            fac//=q
        if largest_prime>R:
            q=largest_prime
            c=n//q
            assert q>c>=1 and n==q*c and mu[n]==-mu[c]
            assert (is_prime==(c==1))
            # Actual high-prime original site = genuine Moebius contribution
            # plus the NONNEGLECTABLE original VF correction.
            correction=weight+mu[c]-int(c==1)
            assert abs(actual-(mu[n]+correction))<1e-13
            high_source_mu+=mu[n]
            high_source_correction+=correction
            physical_high+=actual
            if not is_prime:
                counts["high_composites"]+=1
        else:
            assert not is_prime
            counts["smooth_composites"]+=1
            physical_smooth+=actual

    previous=defect[R]
    next_d=previous-signed
    original_absolute=abs(previous)+absolute
    e=2*next_d*next_d-original_absolute*original_absolute
    upper=(original_absolute-next_d)/2
    lower=(original_absolute+next_d)/2
    assert math.isclose(upper-lower,-next_d,abs_tol=1e-10)
    assert math.isclose(upper+lower,original_absolute,abs_tol=1e-10)
    assert math.isclose(e,upper*upper+lower*lower-6*upper*lower,abs_tol=1e-8)
    assert math.isclose(next_d,defect[R+1],abs_tol=1e-8)
    assert math.isclose(signed,weight*R-counts["primes"],abs_tol=1e-9)
    assert math.isclose(signed,weight*R-mobius_square/2+mobius_signed/2+negative_depth,abs_tol=1e-9)
    assert math.isclose(physical_high,high_source_mu+high_source_correction,abs_tol=1e-9)
    assert math.isclose(physical_high+physical_smooth,signed,abs_tol=1e-9)
    assert counts["primes"]+counts["mu_pos_comp"]+counts["mu_neg_comp"]+counts["squareful"]==R
    if R==317:
        assert counts==dict(primes=54,high_composites=192,smooth_composites=71,
                            mu_pos_comp=132,mu_neg_comp=72,squareful=59)
        assert mobius_square==258 and mobius_signed==6 and negative_depth==72
        assert math.isclose(e,-13423.784662282891,abs_tol=1e-6)
        assert math.isclose(previous,-38.13163607637216,abs_tol=1e-6)
    else:
        assert counts==dict(primes=144,high_composites=659,smooth_composites=224,
                            mu_pos_comp=414,mu_neg_comp=272,squareful=197)
        assert mobius_square==830 and mobius_signed==-2 and negative_depth==272
        assert math.isclose(e,-105561.28136309635,abs_tol=1e-6)
        assert math.isclose(previous,-116.1338540509314,abs_tol=1e-6)
    print(f"R={R} exact_odd_seats={R} prime={counts['primes']} "
          f"high_comp={counts['high_composites']} smooth_comp={counts['smooth_composites']}")
    print(f"  mu_sq={mobius_square} mu_signed={mobius_signed} odd_comp_correction={negative_depth} "
          f"decoded_signed={signed:.12f}")
    print(f"  weight={weight:.12f} high_mu={high_source_mu} high_correction={high_source_correction:.12f} "
          f"physical_high={physical_high:.12f} physical_smooth={physical_smooth:.12f}")
    print(f"  original_Dprev={previous:.12f} original_Dnext={next_d:.12f} "
          f"original_abs={original_absolute:.12f} original_anchored_excess={e:.12f}")
    print(f"  original_UPM={upper:.12f} original_LPM={lower:.12f} "
          f"NNS_normalized={next_d**2/original_absolute**2:.12f}")
print("PASS: sitewise GLOBAL Mobius decoder, full-key high-prime correction, "
      "original VF anchor, UPM/LPM and unmodified NNS denominator")
