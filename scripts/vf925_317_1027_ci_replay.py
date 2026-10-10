#!/usr/bin/env python3
"""#925 integer-by-integer original odd-wheel transport and CoDiv at 317/1027.

Exact prime events via integer smallest-prime-factor sieve. Numerical VF and
wheel densities are deterministic references. No RH or six-sector bound.
"""
import json
import math


def spf_up_to(limit):
    spf=list(range(limit+1))
    for p in range(2,math.isqrt(limit)+1):
        if spf[p]==p:
            for k in range(p*p,limit+1,p):
                if spf[k]==k:spf[k]=p
    return spf


def w(r):return (2*r+1)/(r*math.log(r*r+r+0.5))


def slack(U,L):return 6*U*L-U*U-L*L


def replay():
    roots=(317,1027)
    M=(max(roots)+1)**2
    spf=spf_up_to(M)
    pi=[0]*(M+1)
    for n in range(2,M+1):pi[n]=pi[n-1]+(spf[n]==n)
    VF=[0.]*(max(roots)+2)
    for r in range(2,max(roots)+1):VF[r+1]=VF[r]+r*w(r)
    results=[]
    for R in roots:
        A=R//2+1;B=R+1
        rho=1.0
        for p in range(3,A+1,2):
            if spf[p]==p:rho*=1.0-1.0/p
        P=T=S=N=0
        bias=phase=actual=0.0
        category_count={'prime':0,'old_owner':0,'late_semiprime':0}
        stage_owner_counts={}
        for r in range(A,B):
            wr=w(r)
            for n in range(r*r+1,(r+1)**2):
                if n%2==0:continue
                assert math.isqrt(n)**2!=n
                prime=(spf[n]==n)
                survivor=(spf[n]>A)
                late=survivor and not prime
                if late:
                    p=spf[n];q=n//p
                    assert A<p<q<4*A and spf[q]==q
                assert int(prime)==int(survivor)-int(late)
                N+=1;P+=prime;T+=late;S+=survivor
                category_count['prime' if prime else 'late_semiprime' if late else 'old_owner']+=1
                lhs=int(prime)-wr
                rhs=(rho-wr)+(int(survivor)-rho)-int(late)
                assert abs(lhs-rhs)<2e-15
                bias+=rho-wr;phase+=int(survivor)-rho;actual+=lhs
        assert N==sum(range(A,B))
        assert P==pi[B*B]-pi[A*A]
        assert P+T==S
        assert math.isclose(actual,bias+phase-T,abs_tol=1e-6)
        assert math.isclose(actual,(pi[B*B]-VF[B])-(pi[A*A]-VF[A]),abs_tol=1e-6)
        r=R;wr=w(r);base=pi[r*r]-VF[r];pcount=0;ccount=0
        for n in range(r*r+1,(r+1)**2):
            if n%2:
                if spf[n]==n:pcount+=1
                else:
                    ccount+=1
                    stage_owner_counts[spf[n]]=stage_owner_counts.get(spf[n],0)+1
        assert pcount+ccount==R
        U=max(-base,0.0);L=max(base,0.0)+(1-wr)*R
        parity_slack=slack(U,L)
        owner3_slack=0.0
        for owner,number in sorted(stage_owner_counts.items()):
            for _ in range(number):
                delta=(1-2*wr)+(2+4*wr)*(L-(1-wr))-(6-4*wr)*U
                U+=wr;L-=1-wr
                assert math.isclose(slack(U,L)-delta,
                      slack(U-wr,L+(1-wr)),abs_tol=1e-6)
            if owner==3:owner3_slack=slack(U,L)
        final=slack(U,L)
        assert math.isclose(final,(U+L)**2-2*(pi[(r+1)**2]-VF[r+1])**2,
                            abs_tol=1e-6)
        expected={317:(37842,6897,942,7839,-14.979115047,13423.784662,
                       -10120.580460,25572.580287,106),
                  1027:(396037,59438,6936,66374,-57.832586023,105561.281363,
                        -173464.141270,211608.388513,343)}[R]
        assert (N,P,T,S)==expected[:4]
        for got,want in ((actual,expected[4]),(final,expected[5]),
                         (parity_slack,expected[6]),(owner3_slack,expected[7])):
            assert math.isclose(got,want,abs_tol=1e-3),(R,got,want)
        assert stage_owner_counts[3]==expected[8]
        results.append(dict(R=R,A=A,B=B,physical_odd_sites=N,actual_primes=P,
           true_late_pairs=T,old_owner_composites=category_count['old_owner'],
           frozen_wheel_survivors=S,deterministic_bias=bias,signed_phase=phase,
           signed_prime_VF=actual,owner3_composites=stage_owner_counts[3],
           initial_slack=parity_slack,after_owner3_slack=owner3_slack,
           final_original_codiv_slack=final))
    return results


if __name__=='__main__':
    print(json.dumps(replay(),indent=2))
    print('PASS: all original odd integers at roots 317 and 1027, true sieve, full signed return and CoDiv stage.')
