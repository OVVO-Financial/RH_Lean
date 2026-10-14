#!/usr/bin/env python3
"""Exact integer late-owner wheel census. All strict square endpoints."""
import math,time,bisect
from collections import Counter

def sieve(n):
    a=bytearray(b'\1')*(n+1)
    a[:2]=b'\0\0'
    for i in range(2,math.isqrt(n)+1):
        if a[i]:a[i*i:n+1:i]=b'\0'*(((n-i*i)//i)+1)
    return [i for i in range(n+1) if a[i]],a

def run(A,B,primes,isprime):
    lo=bisect.bisect_right(primes,A)
    s=Counter();window=Counter();exception=None
    for R in range(A,B):
        hi=bisect.bisect_right(primes,R)
        for p in primes[lo:hi]:
            t=R*R//p; u=((R+1)**2-1)//p
            w30=sum(math.gcd(t+j,30)==1 for j in range(1,5))
            c30=sum(math.gcd(q,30)==1 for q in range(t+1,u+1))
            c210=sum(math.gcd(q,210)==1 for q in range(t+1,u+1))
            c2310=sum(math.gcd(q,2310)==1 for q in range(t+1,u+1))
            actual=sum(isprime[q] for q in range(t+1,u+1))
            if not actual <= c2310 <= c210 <= c30 <= w30 <= 2:
                exception=(A,R,p,t,u,actual,c2310,c210,c30,w30)
                break
            s['owners']+=1;s['actual']+=actual;s['W30']+=w30;s['C30']+=c30;s['C210']+=c210;s['C2310']+=c2310
            window[u-t]+=1
        if exception:break
    assert exception is None,exception
    print(f'[{A},{B}): {dict(s)}  window={dict(sorted(window.items()))}  saved_vs_W30={s["W30"]-s["C2310"]}',flush=True)

if __name__=='__main__':
    runs=[(50,100),(100,200),(500,1000),(2634,5267),(5000,10000)]
    ps,isp=sieve(4*max(b for _,b in runs)+40)
    for A,B in runs:
        t=time.monotonic();run(A,B,ps,isp);print('seconds',round(time.monotonic()-t,3),flush=True)
