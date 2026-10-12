// Independent segmented-Mobius prime-comb audit. No RH claim.
// Compile: g++ -O3 -std=c++17 experiments/euler_prime_comb_full_field_audit.cpp -o audit
// Run: ./audit 10000  (supports roots from 2 through 20000)
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using namespace std;

int main(int argc, char** argv) {
    const int R = argc > 1 ? atoi(argv[1]) : 1000;
    if (R < 2 || R > 20000) {cerr << "2<=R<=20000 required\n"; return 2;}
    const int64_t X=1LL*R*R-1;
    const int top=(int)(X/2);
    vector<uint8_t> composite(top+1,0);
    vector<int> smallPrimes;
    for(int i=2;i<=top;i++) {
        if(!composite[i]) {
            if(i<R) smallPrimes.push_back(i);
            if(1LL*i*i<=top)
                for(int64_t j=1LL*i*i;j<=top;j+=i) composite[(int)j]=1;
        }
    }
    vector<int> M(R,0);
    {
        vector<int> rem(R);
        vector<int8_t> mu(R,1);
        for(int i=1;i<R;i++)rem[i]=i;
        for(int p:smallPrimes)
            for(int n=p;n<R;n+=p) {
                int exp=0;
                while(rem[n]%p==0){rem[n]/=p;exp++;}
                if(exp>1)mu[n]=0;
                else if(exp==1)mu[n]=-mu[n];
            }
        for(int n=1;n<R;n++) M[n]=M[n-1]+mu[n];
    }
    int64_t total=0,diag=0,centeredDiag=0,N=0,pos=0,neg=0,zero=0;
    for(int p=R;p<=top;p++) if(!composite[p]) {
        int64_t delta=2LL*(1-M[(int)(X/p)]);
        total+=delta;
        diag+=delta*delta;
        centeredDiag+=(delta-4)*(delta-4);
        N++;
        if(delta>0)pos++; else if(delta<0)neg++; else zero++;
        if(95LL*p>X && delta<0){
            cerr << "Terminal monotonicity failed\n";return 3;
        }
    }
    // Independently compute BOTH M(X) and the intermediate candidate
    // field by segmenting mu(1),...,mu(X). Neither is inferred from
    // the post-root update total or a table of historical endpoints.
    int64_t finalM=0,earlyJ=0,zeros=0;
    const int step=1000000;
    for(int64_t lo=1;lo<=X;lo+=step) {
        const int64_t hi=min(X,lo+step-1);
        const int len=(int)(hi-lo+1);
        vector<uint32_t> rem(len);
        vector<int8_t> mu(len,1);
        for(int i=0;i<len;i++)rem[i]=(uint32_t)(lo+i);
        for(int p:smallPrimes){
            int64_t start=((lo+p-1)/p)*p;
            for(int64_t n=start;n<=hi;n+=p){
                int idx=(int)(n-lo);
                int count=0;
                do {rem[idx]/=p;count++;} while(rem[idx]%p==0);
                if(count>=2)mu[idx]=0;
                else mu[idx]=-mu[idx];
            }
        }
        for(int i=0;i<len;i++){
            int64_t n=lo+i;
            int8_t value=mu[i];
            if(rem[i]>1) value=-value;
            finalM+=value;
            // High-prime composites still have the provisional cofactor
            // sign until their large prime acts on them.
            if(rem[i]>1 && n!=(int64_t)rem[i]) earlyJ-=value;
            else earlyJ+=value;
            if(value==0)zeros++;
        }
    }
    if(earlyJ+total!=finalM){
        cerr << "Failed independent reconstruction: J="<<earlyJ
             <<" plus "<<total<<" != "<<finalM<<"\n";
        return 4;
    }
    double K=1.0;
    for(int y=0;y<R;y++)
        K=max(K,(M[y]-1.0)*(M[y]-1.0)/(y+1.0));
    auto Q=2LL*M[R-1]-finalM;
    cout << "R="<<R<<" X="<<X<<" M(X)="<<finalM
         <<" J_initial="<<earlyJ<<" num_active="<<N
         <<" positive_steps="<<pos<<" negative_steps="<<neg
         <<" zero_steps="<<zero<<"\n";
    cout << "sum_steps="<<total
         <<" initial_plus_4N="<<earlyJ+4*N
         <<" centered_steps="<<total-4*N
         <<" exact_Q="<<Q<<" K="<<K
         <<" observed_C="<<(fabs((double)Q)/(R*sqrt(K)))<<"\n";
    cout << "diag="<<diag<<" diag_over_R2K="<<(diag/(R*(double)R*K))
         <<" centered_diag="<<centeredDiag
         <<" centered_diag_over_R2K="<<(centeredDiag/(R*(double)R*K))
         <<" squareful_zeros="<<zeros<<"\n";
}
