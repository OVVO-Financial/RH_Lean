"""Exact fixed-fibre and physical quarter-envelope obstruction."""
from math import isqrt, gcd
p,q,k,P=13,17,9,2310
n=p**k*q
r=isqrt(n)
L,U=r*r,(r+1)**2-1
A={t:(U-t)//P-(L-1-t)//P for t in range(P) if gcd(t,P)==1}
proper=set()
v=p*p
while v<=U:
    if v>=L:proper.add(v)
    v*=p
for v in proper:A[v%P]-=1
A={t:a for t,a in A.items() if a>0}
B={}
for m in range((L+p**k-1)//p**k,U//p**k+1):
    v=m*p**k
    if gcd(v,P)==1 and v not in proper:B[v%P]=B.get(v%P,0)+1
E=[t for t,b in B.items() if p**k*b>A[t]]
assert len(A)==480 and len(E)==1 and 2**k*len(E)>len(A)
assert sum(A.values())==176452 and 4**k>sum(A.values())
print(dict(p=p,q=q,k=k,n=n,R=r,L=L,U=U,old_fibre_rank=len(A),physical_site_rank=sum(A.values()),exception_rank=len(E)))
