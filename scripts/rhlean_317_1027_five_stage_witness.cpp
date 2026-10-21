// Independent 317/1027 Mobius owner-census witnesses for PR #995.
// Covers ACTUAL integer sites and independently computes prime-owner Fubini sums.
// Does not model the different original #915 VF-weighted clipped carrier.
#include <algorithm>
#include <cassert>
#include <cstdio>
#include <vector>
using namespace std;
static int choose5(int n){ if(n<5)return 0; int a=1;for(int j=1;j<=5;j++)a=a*(n-j+1)/j;return a; }
struct Cohort{long long owners=0, signedHigh=0, absoluteReturn=0;int samplePrime=0;};
int main(){
    constexpr int Max=1027*1027-1;
    vector<int> lp(Max+1), mu(Max+1), omega(Max+1), largest(Max+1), M(Max+1), pi(Max+1), primes;
    mu[1]=1;
    for(int n=2;n<=Max;n++){
        if(!lp[n]){lp[n]=n;mu[n]=-1;omega[n]=1;primes.push_back(n);}
        for(int p:primes){long long m=1LL*n*p; if(m>Max)break;
            lp[m]=p;
            if(n%p==0){mu[m]=0;omega[m]=omega[n];break;}
            mu[m]=-mu[n];omega[m]=omega[n]+1;
        }
    }
    for(int n=1;n<=Max;n++){
        if(n>1)largest[n]=max(lp[n],largest[n/lp[n]]);
        M[n]=M[n-1]+mu[n]; pi[n]=pi[n-1]+(n>=2 && lp[n]==n);
    }
    for(int R : {317,1027}){
        int X=R*R-1;long long smooth=0,high=0,roots=0,children=0,squarefree=0,oddSquarefree=0;
        int maxOmega=0;
        for(int n=1;n<=X;n++){
            if(!mu[n])continue;
            squarefree++;
            if(n%2==1)oddSquarefree++;
            maxOmega=max(maxOmega,omega[n]);
            if(largest[n]<=R)smooth+=mu[n];
            else{high+=mu[n];if(lp[n]==n)roots+=mu[n];else children+=mu[n];}
        }
        Cohort bins[4];long long T=0,A=0,zeroOwners=0;
        for(int q:primes){ if(q<=R)continue; if(q>X)break;
            int k=X/q;int b=k==1?0:k==2?1:k<=9?2:3;auto &c=bins[b];
            if(c.samplePrime==0)c.samplePrime=q;
            c.owners++;c.signedHigh-=M[k];c.absoluteReturn+=abs(M[k]);
            T+=M[k];A+=abs(M[k]); if(M[k]==0)zeroOwners++;
        }
        assert(smooth+high==M[X]);
        assert(high==-T && roots==-(pi[X]-pi[R]));
        assert(high==roots+children);
        assert(bins[1].signedHigh==0 && bins[1].absoluteReturn==0);
        assert(A>=bins[0].owners);
        if(R==317){
            assert(X==100488 && M[X]==-28 && pi[X]==9631);
            assert(smooth==-915 && high==887 && roots==-9565 && children==10452);
            assert(A==9913 && bins[0].owners==4474 && bins[1].owners==1571);
            assert(zeroOwners==1596 && squarefree==61094 && oddSquarefree==40726);
            assert(choose5(maxOmega)==6);
        } else {
            assert(X==1054728 && M[X]==367 && pi[X]==82462);
            assert(smooth==-6602 && high==6969 && roots==-82290 && children==89259);
            assert(A==85539 && bins[0].owners==38831 && bins[1].owners==13531);
            assert(zeroOwners==13831 && squarefree==641207 && oddSquarefree==427473);
            assert(choose5(maxOmega)==21);
        }
        printf("R=%d X=%d M=%d piX=%d piR=%d squarefree=%lld odd_squarefree=%lld\n",R,X,M[X],pi[X],pi[R],squarefree,oddSquarefree);
        printf("  root=%lld high_composite=%lld high=%lld smooth=%lld positive_owner_A=%lld zero_owners=%lld max_depth5=%d\n",roots,children,high,smooth,A,zeroOwners,choose5(maxOmega));
        for(int i=0;i<4;i++){
            const char* label=i==0?"k=1":i==1?"k=2":i==2?"k=3..9":"k>=10";
            printf("  %-7s count=%lld signed_high=%lld owner_abs=%lld example_q=%d\n",label,bins[i].owners,bins[i].signedHigh,bins[i].absoluteReturn,bins[i].samplePrime);
        }
    }
    puts("PASS exact independent sites, unique owner sums, cohorts and depth-5 multiplicities");
}