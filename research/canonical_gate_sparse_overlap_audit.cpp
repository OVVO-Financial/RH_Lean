// Deterministic Mobius census: fixed-height low gate vs high-root owner.
// g++ -O3 -std=c++17 -Wall -Wextra -Werror research/canonical_gate_sparse_overlap_audit.cpp -o /tmp/gate
// /tmp/gate 317 ; /tmp/gate 1027 ; /tmp/gate 3162
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <stdexcept>
#include <vector>
using namespace std;
static long long absll(long long x){return x<0?-x:x;}
int main(int argc,char**argv){
  const int R=argc>1?atoi(argv[1]):3162;
  if(R<3 || R>10000)throw runtime_error("Supported roots: 3..10000");
  const int X=R*R-1;
  vector<uint32_t> least(X+1,0),greatest(X+1,0);
  vector<int8_t> mu(X+1,0);vector<int> primes;
  mu[1]=1;greatest[1]=1;
  for(int i=2;i<=X;i++){
    if(least[i]==0){least[i]=i;primes.push_back(i);mu[i]=-1;}
    for(int p:primes){const uint64_t j=uint64_t(i)*p;
      if(j>uint64_t(X)||p>int(least[i]))break;
      least[j]=p;
      mu[j]=(p==int(least[i]))?0:-mu[i];
    }
    greatest[i]=max(least[i],greatest[i/int(least[i])]);
  }
  const int Lam[]={2,5,10};const int N=3;
  long long signedLow[N]={},countLow[N]={},overlap[N]={},overlapSigned[N]={};
  long long block[N]={},maxBlock[N]={};
  long long M=1,squarefree=1;
  int root=1,nextSquare=4;
  for(int m=2;m<=X;m++){
    while(m>=nextSquare){
      for(int k=0;k<N;k++){maxBlock[k]=max(maxBlock[k],block[k]);block[k]=0;}
      ++root;nextSquare=(root+1)*(root+1);
    }
    const int8_t v=mu[m];M+=v;if(!v)continue;
    ++squarefree;
    const long long q=greatest[m],c=m/q;
    const long long doubleHeight=absll(q*q-c*c);
    for(int k=0;k<N;k++){
      if(doubleHeight<=2LL*Lam[k]*root){
        signedLow[k]+=v;++countLow[k];++block[k];
        if(q>R){++overlap[k];overlapSigned[k]+=v;}
      }
    }
  }
  cout<<"R,X,Lambda,Mtotal,LowSigned,HighSigned,LowCount,HighCount,LowHighCrossSigned,MaxLowInBlock,LowBlockCap,Overlap,OverlapSigned,OverlapCap,CoCross,DivCross\n";
  for(int k=0;k<N;k++){
    maxBlock[k]=max(maxBlock[k],block[k]);
    const long long Dlo=countLow[k],Slo=signedLow[k];
    const long long Dhi=squarefree-Dlo,Shi=M-Slo;
    const long long plo=(Dlo+Slo)/2,nlo=(Dlo-Slo)/2;
    const long long phi=(Dhi+Shi)/2,nhi=(Dhi-Shi)/2;
    const long long coCross=2*(plo*phi+nlo*nhi);
    const long long divCross=2*(plo*nhi+nlo*phi);
    const long long signCross=2*Slo*Shi;
    const long long cap=1LL*Lam[k]*(Lam[k]-1)/2;
    if(maxBlock[k]>Lam[k]+1 || overlap[k]>cap ||
       (Lam[k]==2 && overlap[k]!=0) ||
       coCross-divCross!=signCross ||
       Slo+Shi!=M || plo+nlo!=Dlo || phi+nhi!=Dhi)
       throw runtime_error("Gate or exact reconstruction failure");
    cout<<R<<','<<X<<','<<Lam[k]<<','<<M<<','<<Slo<<','<<Shi<<','<<Dlo<<','<<Dhi
        <<','<<signCross<<','<<maxBlock[k]<<','<<Lam[k]+1<<','<<overlap[k]
        <<','<<overlapSigned[k]<<','<<cap<<','<<coCross<<','<<divCross<<'\n';
  }
  return 0;
}
