#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <string>
#include <vector>
using namespace std;

struct ScanResult {
    int R=0, P=0, K=0;
    long long X=0, j=0, V=0;
    long long finalS=0, finalT=0;
    long double finalEnergy=0;
    int nsteps=0, contracting=0, expanding=0, zero=0;
    long double sumCross=0, sumStep2=0, sumNegDE=0, sumPosDE=0;
    long long maxAbsT=0;
    int maxAbsTp=0;
};

static inline int isqrt_int(int n) {
    int s=(int)std::sqrt((long double)n);
    while (1LL*(s+1)*(s+1)<=n) ++s;
    while (1LL*s*s>n) --s;
    return s;
}

int main(int argc, char** argv){
    if(argc<2){ cerr << "usage: sequential_lpr_test R [R...]\n"; return 2; }
    cout << "R,X,P,K,j,V,steps,contracting,expanding,contract_frac,finalS,finalT,finalE,sumCross,sumStep2,cross_over_step2,maxAbsT,maxAbsTp\n";
    for(int ai=1; ai<argc; ++ai){
        int R=stoi(argv[ai]);
        long long X=1LL*R*R-1;
        if(X > INT32_MAX){ cerr<<"X too large for this exact sieve R="<<R<<"\n"; return 3; }
        int N=(int)X;
        int s=isqrt_int(R);
        int P=R-s;

        vector<uint8_t> isPrime(N+1,1);
        if(N>=0) isPrime[0]=0;
        if(N>=1) isPrime[1]=0;
        for(int i=2;1LL*i*i<=N;i++) if(isPrime[i])
            for(long long m=1LL*i*i;m<=N;m+=i) isPrime[(int)m]=0;
        vector<int> primes;
        primes.reserve((size_t)(N/max(1.0,log((double)max(3,N)))*1.2));
        vector<int32_t> pi(N+1,0);
        int cnt=0;
        for(int n=0;n<=N;n++){
            if(n>=2 && isPrime[n]){ primes.push_back(n); ++cnt; }
            pi[n]=cnt;
        }
        vector<int8_t> mu(N+1,1);
        mu[0]=0;
        vector<int32_t> lpf(N+1,1);
        lpf[0]=0;
        for(int p:primes){
            for(int m=p;m<=N;m+=p){
                if(mu[m]!=0) mu[m] = (int8_t)(-mu[m]);
                lpf[m]=p;
            }
            long long pp=1LL*p*p;
            if(pp<=N) for(long long m=pp;m<=N;m+=pp) mu[(int)m]=0;
        }
        vector<int32_t> M(R+1,0);
        for(int n=1;n<=R;n++) M[n]=M[n-1]+(int)mu[n];

        auto primeCount=[&](long long n)->long long{
            if(n<=0) return 0;
            if(n>N) { cerr<<"primeCount out of range "<<n<<" N="<<N<<"\n"; exit(4); }
            return pi[(int)n];
        };
        auto layerCard=[&](int k)->long long{
            long long lo=max<long long>(R,X/(k+1));
            long long hi=X/k;
            return primeCount(hi)-primeCount(lo);
        };
        long long U=0; int K=0; long long j=0,V=0;
        for(int k=1;k<R;k++){
            long long Nk=layerCard(k);
            long long step=-(long long)M[k];
            long long prev=U;
            U += Nk*step;
            if(K==0 && prev<0 && U>=0){
                if(step<=0){ cerr<<"bad crossing step\n"; exit(5); }
                K=k;
                j=(-prev+step-1)/step;
                if(j>Nk){ cerr<<"j>Nk\n"; exit(6); }
                V=prev+j*step;
            }
        }
        if(K==0){ cerr<<"no crossing R="<<R<<"\n"; return 7; }
        long long NK=layerCard(K);
        long long piR=primeCount(R);
        auto postPrefix=[&](int d)->long long{
            long long U=max<long long>(R,X/d);
            return primeCount(U)-piR;
        };
        long long Hlow=(NK-j)+postPrefix(K+1);

        vector<long long> bucket(P+1,0);
        // Born response: exact c-sum from the Lean definition.
        for(int c=1;c<=N;c++){
            int m=(int)mu[c];
            if(m==0) continue;
            int lp=lpf[c];
            if(lp>P) continue;
            long long upper=min<long long>({(long long)R,(long long)c,X/c});
            long long bc=0;
            if(upper>lp) bc=primeCount(upper)-primeCount(lp);
            if(bc) bucket[lp] += (long long)m*bc;
        }
        // High response: exact c-sum from the Lean definition.
        for(int c=1;c<=R-1;c++){
            int m=(int)mu[c];
            if(m==0) continue;
            int lp=lpf[c];
            if(lp>P) continue;
            long long H = (c<=K) ? Hlow : postPrefix(c);
            if(H) bucket[lp] += (long long)m*H;
        }

        long long S=bucket[1];
        long long T=1-S;
        long double E=(long double)T*(long double)T;
        int steps=0, contracting=0, expanding=0, z=0;
        long double sumCross=0, sumStep2=0, sumNegDE=0, sumPosDE=0;
        long long maxAbsT=llabs(T); int maxAbsTp=1;

        // Detailed prime-by-prime trajectory for this endpoint.
        string fn="sequential_lpr_R"+to_string(R)+".csv";
        FILE* f=fopen(fn.c_str(),"w");
        if(!f){ cerr<<"cannot open detail file "<<fn<<"\n"; return 8; }
        fprintf(f,"p,delta,S_before,S_after,T_before,T_after,cross,step2,dE,contract\n");
        for(int p:primes){
            if(p>P) break;
            long long d=bucket[p];
            long long S0=S, T0=T;
            long double cross=2.0L*(long double)T0*(long double)d;
            long double step2=(long double)d*(long double)d;
            S += d;
            T = 1-S;
            long double Enew=(long double)T*(long double)T;
            long double dE=Enew-E;
            int contr=(dE<0)?1:((dE>0)?-1:0);
            if(dE<0){ contracting++; sumNegDE += -dE; }
            else if(dE>0){ expanding++; sumPosDE += dE; }
            else z++;
            sumCross += cross; sumStep2 += step2;
            E=Enew; steps++;
            if(llabs(T)>maxAbsT){ maxAbsT=llabs(T); maxAbsTp=p; }
            fprintf(f,"%d,%lld,%lld,%lld,%lld,%lld,%.0Lf,%.0Lf,%.0Lf,%d\n",
                p,d,S0,S,T0,T,cross,step2,dE,contr);
        }
        fclose(f);

        cout<<R<<','<<X<<','<<P<<','<<K<<','<<j<<','<<V<<','<<steps<<','<<contracting<<','<<expanding<<','
            <<setprecision(8)<<(steps?((double)contracting/steps):0.0)<<','<<S<<','<<T<<','
            <<fixed<<setprecision(0)<<E<<','<<sumCross<<','<<sumStep2<<','
            <<setprecision(8)<<(sumStep2!=0?(double)(sumCross/sumStep2):numeric_limits<double>::quiet_NaN())<<','
            <<maxAbsT<<','<<maxAbsTp<<"\n";
        cerr<<"done R="<<R<<" K="<<K<<" P="<<P<<" final T="<<T<<" detail="<<fn<<"\n";
    }
}
