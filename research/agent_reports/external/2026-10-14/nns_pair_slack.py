import math
from decimal import Decimal, getcontext
from fractions import Fraction
getcontext().prec = 55

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    if n % 3 == 0: return n == 3
    k = 5
    while k*k <= n:
        if n%k == 0 or n%(k+2)==0: return False
        k += 6
    return True

def w(r):
    rr = Decimal(r)
    return (2*rr+1)/(rr*(rr*rr+rr+Decimal('0.5')).ln())

def run(R):
    bottom,top=R*R,(R+1)*(R+1)
    rows=[]
    for n in range(bottom+1,top):
        if n%3: continue
        q=n//3
        if not is_prime(q): continue
        r=math.isqrt(q)
        assert r*r<q<(r+1)*(r+1)
        x=w(R); y=Decimal(1)-w(r)
        slack=6*x*y-x*x-y*y
        rows.append((R,n,q,r,slack,x,y))
    return rows

for R in (1010,1011,1012,1024,2048,2049,2050,3072,4096,5000):
    rows=run(R)
    print('R=', R, 'physical_pairs=',len(rows),'max_slack=',max((t[4] for t in rows),default=None),'min_slack=',min((t[4] for t in rows),default=None),'nonnegative=',sum(x[4]>=0 for x in rows))
    if R in (1011,2048) and rows:
        print('first',rows[0][:5])
print('R1011 exact witness:',[x for x in run(1011) if x[2]==340709])
x=Fraction(9,64); y=Fraction(541,640)
print('symbolic_certificate', {'x_upper':str(x),'y_lower':str(y),'y_minus_6x_lower':str(y-6*x),'pair_slack_upper':str(-(y*(y-6*x)))})
