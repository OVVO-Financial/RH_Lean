"""Native factorial-denominator certificates; exact small cases, floating log diagnostics."""
import math, itertools, json
from fractions import Fraction
import numpy as np
from scipy.special import gammaln

def small_checks():
 for m in (2,3,4):
  N=m*m-1
  L=m*N
  A=1;lc=1
  for j in range(1,L+1):
   if (j-1)%m==0:lc=math.lcm(lc,max(1,(j-1)//m))
   A*=math.gcd(j,lc)
  C=math.factorial(N)**m//A
  fact=[math.factorial(i) for i in range(L+1)]
  tuples=0; full=1; grid=1
  for a in range(N):
   u=Fraction(fact[N]**m,fact[m*a]*fact[N-a-1]**m)
   assert C%u.numerator==0
   full=math.lcm(full,u.numerator)
   if a%m==0:grid=math.lcm(grid,u.numerator)
  for aa in itertools.product(range(N),repeat=m):
   r=Fraction(fact[sum(aa)]*math.prod(fact[N-a-1] for a in aa),fact[N]**m)
   assert C%r.denominator==0;tuples+=1
  for p in range(m+1,N+1):
   if all(p%d for d in range(2,math.isqrt(p)+1)):
    k=C;v=0
    while k%p==0:k//=p;v+=1
    k=full;w=0
    while k%p==0:k//=p;w+=1
    assert v==w
  print(json.dumps({'exact':True,'R':m,'N':N,'tuple_checks':tuples,'full_family_divides_C':C%full==0,'grid_family_divides_C':C%grid==0}),flush=True)

def beta_matrix(m):
 N=m*m-1; a=m*np.arange(m,dtype=np.int64);a[-1]-=1
 # B[i,j]=(a_i+j)!(N-a_i-j-1)!/N!, a_i+j<=N-1.
 # det B= prod_i a_i! (N-a_i-m)!/N! * Vandermonde(a) * prod_{k=0}^{m-2}(N-k)^(m-1-k)
 logdet=float(np.sum(gammaln(a+1)+gammaln(N-a-m+1)-gammaln(N+1)))
 logdet+=float(np.sum(np.arange(m-1,0,-1)*np.log(N-np.arange(m-1))))
 for i in range(m-1):logdet+=float(np.log(a[i+1:]-a[i]).sum())
 if m<=8:
  B=[[Fraction(math.factorial(int(x)+j)*math.factorial(N-int(x)-j-1),math.factorial(N)) for j in range(m)] for x in a]
  det=Fraction(1)
  for i in range(m):
   pivot=B[i][i];assert pivot;det*=pivot
   for j in range(i+1,m):
    v=B[j][i]/pivot
    for k in range(i+1,m):B[j][k]-=v*B[i][k]
  exact=Fraction(math.prod(math.factorial(int(x))*math.factorial(N-int(x)-m) for x in a)*math.prod((N-k)**(m-1-k) for k in range(m-1))*math.prod(int(a[j]-a[i]) for i in range(m) for j in range(i+1,m)),math.factorial(N)**m)
  assert det==exact
 return -logdet/(m*N)

def selberg(m):
 N=m*m-1; j=np.arange(m); best=(0,None,None)
 for k in range((N-1)//(2*(m-1))+1):
  maxa=N-1-2*k*(m-1)
  def val(a):
   b=maxa-a;A=m*a+k*m*(m-1)
   return float(gammaln(A+1)+np.sum(gammaln(b+1+j*k)+gammaln(1+(j+1)*k)-gammaln(1+k))-m*gammaln(N+1))
  # convex in a: derivative increasing (sum of positive trigamma terms)
  lo,hi=0,maxa
  while hi-lo>3:
   c=lo+(hi-lo)//3;d=hi-(hi-lo)//3
   if val(c)<=val(d):hi=d
   else:lo=c
  a=min(range(lo,hi+1),key=val);v=val(a)
  if v<best[0]:best=(v,a,k)
 return -best[0]/(m*N),best[1],best[2]
if __name__=='__main__':
 small_checks()
 for m in (4,8,16,32,64,128,317,1027,2048,4096):
  v,a,k=selberg(m)
  print(json.dumps({'R':m,'beta_grid_logdet_normalized':beta_matrix(m),'best_pooled_vandermonde_log_inverse_normalized':v,'best_a':a,'best_k':k}),flush=True)
