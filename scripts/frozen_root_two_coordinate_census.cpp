// Source-faithful prime-2 root-half bilinear audit.
// Computes only mu(1),...,mu(R-1), never any mu value above sqrt(X).
// All row contributions use the exact original X=R*R-1.
// No prime-count or analytic bound is assumed.
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <vector>
using namespace std;
int main() {
  constexpr int MaxR = 10000;
  vector<int> mu(MaxR+1, 1), primes, composite(MaxR+1), M(MaxR+1);
  mu[0]=0;
  for (int n=2;n<=MaxR;n++) {
    if (!composite[n]) { primes.push_back(n); mu[n]=-1; }
    for (int p:primes) {
      if ((int64_t)n*p>MaxR) break;
      composite[n*p]=1;
      if (n%p==0) { mu[n*p]=0; break; }
      mu[n*p]=-mu[n];
    }
  }
  for (int n=1;n<=MaxR;n++) M[n]=M[n-1]+mu[n];
  for (int R: {31,137,317,1027,5561,10000}) {
    const int64_t X=(int64_t)R*R-1;
    int64_t LL=0,LH=0,HH=0,H1=0,H2=0,H3=0,highOdd=0;
    vector<int> odd;
    for (int m=1;m<R;m+=2) {
      if (!mu[m]) continue;
      odd.push_back(m);
      if (2*m>=R) highOdd+=mu[m];
    }
    for (int m:odd) for (int n:odd) {
      const int64_t den=(int64_t)m*n,sgn=mu[m]*mu[n];
      const int hm=(2*m<R),hn=(2*n<R);
      const int64_t z=X/den;
      const int64_t kernel=z-(hm+hn)*(X/(2*den))+hm*hn*(X/(4*den));
      if (hm && hn) LL+=sgn*kernel;
      else if (!hm && !hn) {
        HH+=sgn*kernel;
        H1+=sgn;
        H2+=sgn*(z>=2);
        H3+=sgn*(z>=3);
        assert(z>=1 && z<=3);
      } else LH+=sgn*kernel;
    }
    const int64_t Q=LL+LH+HH;
    const int64_t reconstructed=2*M[R-1]-Q;
    assert(highOdd==M[R-1] && H1==(int64_t)M[R-1]*M[R-1]);
    assert(HH==H1+H2+H3);
    switch (R) {
      case 31: assert(Q==-10 && reconstructed==4);break;
      case 137: assert(Q==-2 && reconstructed==0);break;
      case 317: assert(LL==29 && LH==-32 && H1==9 && H2==4 &&
                       H3==12 && Q==22 && reconstructed==-28);break;
      case 1027:assert(LL==-179 && LH==-70 && H1==16 && H2==-73 &&
                       H3==-69 && Q==-375 && reconstructed==367);break;
      case 5561:assert(LL==484 && LH==1106 && H1==25 && H2==462 &&
                       H3==477 && Q==2554 && reconstructed==-2544);break;
      case 10000:assert(LL==654 && LH==-2314 && H1==529 && H2==-831 &&
                        H3==-12 && Q==-1974 && reconstructed==1928);break;
    }
    double K=0;
    for (int y=0;y<R;y++) K=max(K,double((M[y]-1)*(M[y]-1))/(y+1));
    cout<<"PASS R="<<R<<" Q="<<Q<<" reconstructed_M="<<reconstructed
        <<" K="<<setprecision(8)<<K<<" C="<<fabs(double(Q))/(R*sqrt(K))<<"\n";
  }
}
