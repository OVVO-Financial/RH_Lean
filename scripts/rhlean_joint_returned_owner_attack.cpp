// Native RH_Lean greatest-prime owner / fixed-depth history audit.
// Independent integer-exact Mobius sieve; no RH or analytic estimates assumed.
// g++ -O3 -std=c++17 scripts/rhlean_joint_returned_owner_attack.cpp -o /tmp/rhlean_joint_owner_audit
// /tmp/rhlean_joint_owner_audit
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <vector>
using namespace std;
long long binom(int n,int k){if(k>n)return 0;long long r=1;for(int j=1;j<=k;j++)r=r*(n-j+1)/j;return r;}
int main(){
    const int Rmax=3162, N=Rmax*Rmax-1;
    vector<int> lp(N+1),mu(N+1),M(N+1),pi(N+1),omega(N+1),primes;
    mu[1]=1;
    for(int n=2;n<=N;n++){
        if(!lp[n]){lp[n]=n;primes.push_back(n);mu[n]=-1;omega[n]=1;}
        for(int p:primes){long long m=1LL*n*p;if(m>N)break;
            lp[m]=p;
            if(n%p==0){mu[m]=0;omega[m]=omega[n];break;}
            mu[m]=-mu[n];omega[m]=omega[n]+1;
        }
    }
    for(int n=1;n<=N;n++){M[n]=M[n-1]+mu[n];pi[n]=pi[n-1]+(n>=2&&lp[n]==n);}
    for(int R:{100,317,1027,3162}){
        int X=R*R-1; long long T=0,A=0,k1=0,k2=0,zeros=0,highOwners=0;
        for(int p:primes){if(p>X)break;if(p<=R)continue;
            int k=X/p; T+=M[k];A+=abs(M[k]);highOwners++;
            if(k==1)k1++;
            if(k==2){k2++; if(M[k]!=0){puts("ERROR k=2");return 1;}}
            if(M[k]==0)zeros++;
        }
        long long smooth = M[X]+T;
        long long positiveRoot = (long long)pi[X]-pi[X/2];
        if(positiveRoot!=k1 || A<k1 || smooth-T!=M[X]){puts("ERROR mass/fiber identity");return 1;}
        int depth5max=0, at=1, maxw=0;
        for(int n=1;n<=X;n++)if(mu[n]!=0){
            if(omega[n]>maxw)maxw=omega[n];
            int c5=(int)binom(omega[n],5);
            if(c5>depth5max){depth5max=c5;at=n;}
        }
        printf("R=%d X=%d M=%d prime_owners=%lld\n",R,X,M[X],highOwners);
        printf("  positive_root_k1=%lld exact_pi_interval=%lld  k2_cancelled=%lld  zero_M_owners=%lld\n",k1,positiveRoot,k2,zeros);
        printf("  positive_fiber_mass_A=%lld >= k1=%lld  signed_prime_fiber_T=%lld\n",A,k1,T);
        printf("  high_prime_signed_H=-T=%lld  smooth_signed_S=%lld  S-T=M=%lld\n",-T,smooth,smooth-T);
        printf("  max_distinct_prime_factors=%d max_five_level_histories=%d at_n=%d\n",maxw,depth5max,at);
    }
}
