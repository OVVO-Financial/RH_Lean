// Genuine-Mobius square window and shared-gcd sampler, integer exact.
// No simulated signs, nonstandard axiom, PNT, independence, or polynomial gain.
#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

using i64 = int64_t;

i64 numerator(int r,int d) {
  const i64 x=i64(r)*r-1, y=i64(r)*r+2*r;
  return x%d-y%d;
}
i64 historical(int R,const std::vector<int8_t>& mu) {
  const i64 x=i64(R)*R-1, y=i64(R)*R+2*R;
  i64 w=0;
  for(int b=1;b<R;++b) if(mu[b])
    for(int a=1;a<R;++a) if(mu[a]) {
      const i64 d=i64(a)*b;
      w+=i64(mu[a])*mu[b]*(y/d-x/d);
    }
  return w;
}
void check_gcd_covariance(int d,int e) {
  const int g=std::gcd(d,e),a=d/g,b=e/g,L=g*a*b;
  i64 full=0,conditional=0;
  for(int r=0;r<L;++r)full+=numerator(r,d)*numerator(r,e);
  for(int t=0;t<g;++t) {
    i64 A=0,B=0;
    for(int k=0;k<a;++k)A+=numerator(t+g*k,d);
    for(int k=0;k<b;++k)B+=numerator(t+g*k,e);
    conditional+=A*B;
  }
  assert(full==conditional);  // exact CRT, all shared gcd classes retained
  if(g==1)assert(full==0);
  if((d==2&&e==4)||(d==6&&e==14)) {
    const double c=double(full)/(double(L)*d*e);
    std::cout<<"shared d="<<d<<" e="<<e<<" g="<<g
             <<" completeCov="<<c<<"\n";
  }
}
int main(){
  const int Rmax=4096,N=(Rmax+1)*(Rmax+1)-1;
  std::vector<int8_t> mu(N+1,1);
  mu[0]=0;
  std::vector<uint8_t> prime(N+1,1);
  prime[0]=prime[1]=0;
  for(int p=2;i64(p)*p<=N;++p)if(prime[p])
    for(i64 n=i64(p)*p;n<=N;n+=p)prime[n]=0;
  for(int p=2;p<=N;++p)if(prime[p]){
    for(i64 n=p;n<=N;n+=p)mu[n]=-mu[n];
    if(i64(p)*p<=N)
      for(i64 n=i64(p)*p;n<=N;n+=i64(p)*p)mu[n]=0;
  }
  for(int R=3;R<=75;++R){
    i64 delta=0;
    for(i64 n=i64(R)*R;n<=i64(R)*R+2*R;++n)delta+=mu[n];
    const i64 gate=i64(mu[R])*mu[R]+
      2LL*mu[R]*(mu[R+1]+mu[R+2]);
    const i64 w=historical(R,mu);
    assert(std::abs(gate)<=5);
    assert(delta==gate-w);
  }
  for(int R : {317,1027,2048,4096}){
    i64 delta=0;
    for(i64 n=i64(R)*R;n<=i64(R)*R+2*R;++n)delta+=mu[n];
    const i64 gate=i64(mu[R])*mu[R]+
      2LL*mu[R]*(mu[R+1]+mu[R+2]);
    const i64 w=historical(R,mu);
    assert(delta==gate-w);
    double harmonic=0;
    for(int a=1;a<R;++a) harmonic+=double(mu[a])/a;
    const double drift=(2.*R+1)*harmonic*harmonic;
    std::cout<<"R="<<R<<" shell="<<delta<<" gate="<<gate
             <<" historical="<<w<<" harmonicDrift="<<drift
             <<" centeredSigned="<<double(w)-drift<<"\n";
  }
  for(int d=1;d<=50;++d)for(int e=1;e<=50;++e)
    check_gcd_covariance(d,e);
  check_gcd_covariance(6,14);
  for(int H : {32,64,128,256,512,1024,2048,4096}){
    const int d=3*H/2,e=d+1; // coprime but lcm ~= H^2
    double sum=0;
    for(int r=H;r<2*H;++r)
      sum+=double(numerator(r,d))*numerator(r,e)/double(d*e);
    std::cout<<"H="<<H<<" adjacentCoprime="<<d<<","<<e
             <<" incompleteMean="<<sum/H<<"\n";
  }
  std::cout<<"PASS exact gate, CRT gcd-residue covariance, coprime full-period"
           " cancellation, and long-incomplete-period diagnostic\n";
}
