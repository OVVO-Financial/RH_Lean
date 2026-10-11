// Exact cofactor-conditioned prime-availability census for RH_Lean finite-C.
// Standard library only. g++ -O3 -std=c++17 ... -o census && ./census [MAX_ROOT]
// Run: ./census 6000 .  (root ceiling then output directory)
// Outputs root_features.csv, selected_owner_groups.csv, selected_depth.csv,
// selected_gcd_overlap.csv, selected_dyadic.csv, selected_prime_updates.csv.
// Uses actual mu and pi, and cross-checks the historical floor identity.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <numeric>
#include <string>
#include <tuple>
#include <vector>
using namespace std;
using ll=long long;
static ll ab(ll x){return x<0?-x:x;}
int main(int argc,char **argv){
    const int MAXR=argc>1?atoi(argv[1]):6000;
    if(MAXR<56||MAXR>10000){cerr<<"56<=MAXR<=10000 required\n";return 2;}
    const int XMAX=MAXR*MAXR-1;
    cerr<<"Sieve to "<<XMAX<<"...\n";
    vector<uint32_t> spf(XMAX+1),lpf(XMAX+1),pi(XMAX+1);
    vector<int8_t> mu(XMAX+1);vector<uint32_t> primes;
    mu[1]=1;lpf[1]=1;
    for(int n=2;n<=XMAX;n++){
        if(!spf[n]){spf[n]=n;mu[n]=-1;primes.push_back(n);}
        for(uint32_t p:primes){ll v=1LL*p*n;if(v>XMAX||p>spf[n])break;
            spf[v]=p;
            if(p==spf[n]){mu[v]=0;break;}
            mu[v]=-mu[n];
        }
    }
    cerr<<"Sieve done. primes "<<primes.size()<<". Computing LPF and pi...\n";
    vector<int> mertensAtX(MAXR+1,0);
    int currentM=0,nextR=2;
    for(int n=1;n<=XMAX;n++){
        if(n>1) lpf[n]=max(spf[n],lpf[n/spf[n]]);
        pi[n]=pi[n-1]+(n>1&&spf[n]==(uint32_t)n);
        currentM+=mu[n];
        if(nextR<=MAXR && 1LL*nextR*nextR-1==n) {mertensAtX[nextR]=currentM;nextR++;}
    }
    vector<int> smallM(MAXR+1,0);
    for(int n=1;n<=MAXR;n++)smallM[n]=smallM[n-1]+mu[n];
    if((MAXR>=100 && smallM[100]!=1) ||
       (MAXR>=1000 && smallM[1000]!=2) ||
       (MAXR>=317 && mertensAtX[317]!=-28)){
        cerr<<"Sanity check failed";return 3;
    }
    vector<int> coprimeSigned(MAXR+1,0),coprimeUnsigned(MAXR+1,0);
    // Earlier cofactors c<d, c>=2 that are coprime with d.
    for(int d=2;d<=MAXR;d++)for(int c=2;c<d;c++)
        if(mu[c] && gcd(c,d)==1){coprimeSigned[d]+=mu[c];coprimeUnsigned[d]++;}
    const vector<int> chosen={56,317,1000,2000,5561,6000};
    string dir=(argc>2?argv[2]:".");
    if(!dir.empty()&&dir.back()!='/')dir+='/';
    ofstream out(dir+"root_features.csv"), owner(dir+"selected_owner_groups.csv"),
      depth(dir+"selected_depth.csv"), gd(dir+"selected_gcd_overlap.csv"),
      dy(dir+"selected_dyadic.csv"), steps(dir+"selected_prime_updates.csv"), shg(dir+"selected_smooth_high_gcd.csv");
    out<<"R,X,M_X,M_R_minus_1,Q_R,K_R,C_R,A_R,squarefree_cofactors,positive_cofactors,negative_cofactors,highprime_pi_count,highprime_total_signed,highprime_total_abs,highprime_positive_exposures,highprime_negative_exposures,weighted_parity_mean,unweighted_parity_mean,independent_prediction_B,conditional_covariance_correction,smooth_mass,sign_cdf_gap_min,sign_cdf_gap_max,sign_cdf_crosses,centered_owner_prime_sum,centered_owner_prime_diagonal,same_prime_cross_all,same_prime_cross_gcd1,same_prime_cross_shared,gcd1_pair_unsigned,gcd_shared_pair_unsigned,owner_distinct_cross\n";
    owner<<"R,largest_prime_owner,smooth_signed,highprime_signed,combined_signed,smooth_abs,highprime_abs\n";
    depth<<"R,omega_depth,smooth_signed,smooth_count,highprime_signed,highprime_count,combined_signed\n";
    gd<<"R,gcd_stratum,same_prime_cross_signed,same_prime_cross_positive,same_prime_cross_negative,same_prime_abs_total,gcd1_weighted_bias\n";
    dy<<"R,cofactor_dyadic_lo,cofactor_dyadic_hi,plus_count,minus_count,plus_extensions,minus_extensions,signed_extension_mass,unsigned_extension_mass\n";
    steps<<"R,active_primes,positive_steps,negative_steps,zero_steps,sum_steps,J_initial,final_M,diagonal_sum_of_update_squares\n";
    shg<<"R,smooth_mass,highprime_mass,full_smooth_high_cross,coprime_ancestry_cross,shared_ancestry_cross,shared_ratio_to_absolute_cross,nonzero_smooth_count\n";
    out<<setprecision(17);
    cerr<<"Scanning cofactor availability for all roots...\n";
    for(int R=2;R<=MAXR;R++){
        int X=R*R-1; ll signedB=0,absB=0,plusB=0,minusB=0,nonzero=0,positive=0,negative=0;
        vector<ll> a(R),N(R);
        for(int c=1;c<R;c++){
            N[c]=static_cast<ll>(pi[X/c])-pi[R-1];
            a[c]=static_cast<ll>(mu[c])*N[c];
            signedB+=a[c]; absB+=ab(a[c]);
            if(mu[c]!=0){nonzero++;if(mu[c]==1){positive++;plusB+=N[c];}else{negative++;minusB+=N[c];}}
        }
        int px=pi[X]-pi[R-1];
        ll smooth = static_cast<ll>(mertensAtX[R])+signedB;
        double K=1.0;
        for(int k=1;k<R;k++)K=max(K,(smallM[k]-1.)*(smallM[k]-1.)/(k+1.));
        ll Q=2LL*smallM[R-1]-mertensAtX[R];
        double C=ab(Q)/(R*sqrt(K)), A=(mertensAtX[R]-1.)*(mertensAtX[R]-1.)/(1.*R*R*K);
        // Exact CDF dominance of available prime counts when conditioning on mu=+/-.
        int pp=0,mm=0; ll minGap=0,maxGap=0;bool seenP=false,seenN=false;
        for(int c=1;c<R;c++){
            if(mu[c]==1)pp++;
            else if(mu[c]==-1)mm++;
            ll v=1LL*pp*negative-1LL*mm*positive;
            minGap=min(minGap,v);maxGap=max(maxGap,v);
            if(v>0)seenP=true;
            if(v<0)seenN=true;
        }
        double avgN=nonzero?double(absB)/nonzero:0.0;
        double muAvg=nonzero?double(positive-negative)/nonzero:0.0;
        double indB=(positive-negative)*avgN;
        double corr=signedB-indB;
        // Exposure-overlap Gram: |A_c cap A_d|=N(max(c,d)), where
        // A_c = {p prime >=R: cp<=X}. Centering excludes cofactor 1.
        ll colsum=signedB-N[1]; ll colnorm=0,diag=0,cross1=0,crossShared=0;
        ll unsignedG1=0,unsignedGShared=0;
        // All-root conditional overlap moments in O(R), no pair enumeration.
        ll diagAll=0,crossAllR=0,cross1All=0, unsignedAllR=0,unsigned1All=0;
        int countNonzeroBefore=0;
        for(int d=2;d<R;d++)if(mu[d]){
            diagAll+=N[d];
            crossAllR+=2LL*mu[d]*N[d]*(smallM[d-1]-1);
            cross1All+=2LL*mu[d]*N[d]*coprimeSigned[d];
            unsignedAllR+=2LL*N[d]*countNonzeroBefore;
            unsigned1All+=2LL*N[d]*coprimeUnsigned[d];
            countNonzeroBefore++;
        }
        ll crossSharedAll=crossAllR-cross1All;
        ll colnormAll=diagAll+crossAllR;
        ll cross1Positive=0,cross1Negative=0,crossSharedPositive=0,crossSharedNegative=0;
        if(binary_search(chosen.begin(),chosen.end(),R)){
            for(int c=2;c<R;c++) if(mu[c])diag+=N[c];
            for(int d=3;d<R;d++)if(mu[d]) for(int c=2;c<d;c++)if(mu[c]){
                ll weighted=2LL*N[d];
                bool common=gcd(c,d)>1;
                bool same=mu[c]==mu[d];
                if(common){unsignedGShared+=weighted;crossShared+=same?weighted:-weighted;
                   (same?crossSharedPositive:crossSharedNegative)+=weighted;
                }else{unsignedG1+=weighted;cross1+=same?weighted:-weighted;
                   (same?cross1Positive:cross1Negative)+=weighted;
                }
            }
            colnorm=diag+cross1+crossShared;
            if(diagAll!=diag||colnormAll!=colnorm||cross1All!=cross1||crossSharedAll!=crossShared||unsignedAllR-unsigned1All!=unsignedGShared||unsigned1All!=unsignedG1){
                cerr<<"Cross-check divisor O(R) identity failed R="<<R<<"\n";return 7;
            }
            ll directly=0, firstCorrectionSum=0, correctionEnergy=0;
            ll active=0,posStep=0,negStep=0,zeroStep=0;
            for(uint32_t p:primes){if(p<(uint32_t)R)continue;if(p>(uint32_t)(X/2))break;
                int k=X/p;
                ll v=smallM[k]-1;
                directly+=v*v;
                ll del=-2*v;firstCorrectionSum+=del;correctionEnergy+=del*del;
                active++;
                if(del>0)posStep++;else if(del<0)negStep++;else zeroStep++;
            }
            if(directly!=colnorm||(-2*colsum)!=firstCorrectionSum){cerr<<"Gram check failure "<<R<<" "<<directly<<" "<<colnorm<<" "<<colsum<<" "<<firstCorrectionSum<<"\n";return 4;}
            ll J=mertensAtX[R]-firstCorrectionSum;
            steps<<R<<','<<active<<','<<posStep<<','<<negStep<<','<<zeroStep<<','<<firstCorrectionSum<<','<<J<<','<<mertensAtX[R]<<','<<correctionEnergy<<'\n';
            gd<<R<<",coprime,"<<cross1<<','<<cross1Positive<<','<<cross1Negative<<','<<unsignedG1<<','<<(unsignedG1?double(cross1)/unsignedG1:0)<<'\n';
            gd<<R<<",shared_gcd,"<<crossShared<<','<<crossSharedPositive<<','<<crossSharedNegative<<','<<unsignedGShared<<','<<(unsignedGShared?double(crossShared)/unsignedGShared:0)<<'\n';
            gd<<R<<",combined,"<<(cross1+crossShared)<<','<<(cross1Positive+crossSharedPositive)<<','<<(cross1Negative+crossSharedNegative)<<','<<(unsignedG1+unsignedGShared)<<','<<(unsignedG1+unsignedGShared?double(cross1+crossShared)/(unsignedG1+unsignedGShared):0)<<'\n';
            cerr<<"R="<<R<<" Q="<<Q<<" B="<<signedB<<" smooth="<<smooth<<" same-prime-Gram="<<colnorm<<" gcd-1-cross="<<cross1<<" gcd>1-cross="<<crossShared<<"\n";
            // Exact smooth grouping by largest prime factor; each n belongs once.
            vector<ll> Sowner(R+1,0),Howner(R+1,0),absSmooth(R+1,0),absHigh(R+1,0);
            vector<ll> Sdepth(14),Hdepth(14),SdepthCount(14),HdepthCount(14);
            for(int n=1;n<=X;n++) if(mu[n]&&lpf[n]<(uint32_t)R){
                int v=lpf[n];Sowner[v]+=mu[n];absSmooth[v]++;
                int omega=0,j=n;
                while(j>1){omega++;j/=spf[j];}
                if(omega>=(int)Sdepth.size()){cerr<<"Depth too large";return 6;}
                Sdepth[omega]+=mu[n];SdepthCount[omega]++;
            }
            for(int c=1;c<R;c++)if(mu[c]){
                int v=lpf[c];Howner[v]-=a[c];absHigh[v]+=N[c];
                int omega=0,j=c;while(j>1){omega++;j/=spf[j];}
                Hdepth[omega+1]-=a[c];HdepthCount[omega+1]+=N[c];
            }
            ll s2=0,h2=0;
            for(int v=1;v<R;v++)if(absSmooth[v]||absHigh[v]){
                owner<<R<<','<<v<<','<<Sowner[v]<<','<<Howner[v]<<','<<Sowner[v]+Howner[v]<<','<<absSmooth[v]<<','<<absHigh[v]<<'\n';
                s2+=Sowner[v];h2+=Howner[v];
            }
            for(int j=0;j<(int)Sdepth.size();j++)if(SdepthCount[j]||HdepthCount[j]){
                depth<<R<<','<<j<<','<<Sdepth[j]<<','<<SdepthCount[j]<<','<<Hdepth[j]<<','<<HdepthCount[j]<<','<<Sdepth[j]+Hdepth[j]<<'\n';
            }
            if(s2!=smooth||h2!=-signedB||s2+h2!=mertensAtX[R]){cerr<<"Owner parity failure R="<<R<<" S="<<s2<<" H="<<h2<<" M="<<mertensAtX[R]<<" expected S="<<smooth<<" B="<<signedB<<"\n";return 5;}
            // Exact smooth/high pair covariance by shared cofactor ancestry.
            // For high m=p*c and root-smooth n, gcd(m,n)=gcd(c,n).
            // Euler-Mobius inversion of the coprime indicator:
            // 1_{gcd(c,n)=1}=sum_{d|c,d|n} mu(d).
            vector<int8_t> smoothField(X+1,0);
            ll smoothCnt=0;
            for(int n=1;n<=X;n++)if(mu[n]&&lpf[n]<(uint32_t)R){
                smoothField[n]=mu[n];smoothCnt++;
            }
            vector<ll> smoothDiv(R,0), coprimeSmooth(R,0);
            for(int d=1;d<R;d++)if(mu[d]){
                ll sm=0;
                for(int n=d;n<=X;n+=d)sm+=smoothField[n];
                smoothDiv[d]=sm;
            }
            if(smoothDiv[1]!=smooth){cerr<<"Smooth divisor 1 sum mismatch R="<<R<<"\n";return 8;}
            for(int d=1;d<R;d++)if(mu[d]){
                ll term=mu[d]*smoothDiv[d];
                for(int c=d;c<R;c+=d)coprimeSmooth[c]+=term;
            }
            ll covCoprime=0;
            for(int c=1;c<R;c++)if(mu[c]) covCoprime-=a[c]*coprimeSmooth[c];
            ll covTotal=smooth*(-signedB);
            ll covShared=covTotal-covCoprime;
            if(R==56){
                ll bruteCop=0,bruteShared=0;
                for(int m=1;m<=X;m++)if(smoothField[m])
                    for(int n=2;n<=X;n++)if(mu[n]&&lpf[n]>=(uint32_t)R){
                        ll w=mu[m]*mu[n];
                        if(gcd(m,n)==1)bruteCop+=w;else bruteShared+=w;
                    }
                if(bruteCop!=covCoprime||bruteShared!=covShared){
                    cerr<<"Direct physical smooth/high pair identity failure"<<"\n";return 9;
                }
                cerr<<"  R=56 independent brute-force smooth/high pair gcd PASS"<<"\n";
            }
            shg<<R<<','<<smooth<<','<<-signedB<<','<<covTotal<<','<<covCoprime<<','<<covShared<<','<<(covTotal?double(covShared)/covTotal:0)<<','<<smoothCnt<<'\n';
            cerr<<"  smooth/high gcd cross: total="<<covTotal<<" coprime="<<covCoprime<<" shared="<<covShared<<"\n";
            // Dyadic cofactor intervals, signed N availability.
            for(int lo=1;lo<R;lo*=2){int hi=min(R-1,lo*2-1);ll pc=0,mc=0,pt=0,mt=0;
                for(int c=lo;c<=hi;c++)if(mu[c]==1){pc++;pt+=N[c];}else if(mu[c]==-1){mc++;mt+=N[c];}
                dy<<R<<','<<lo<<','<<hi<<','<<pc<<','<<mc<<','<<pt<<','<<mt<<','<<pt-mt<<','<<pt+mt<<'\n';
            }
        }
        ll crossAll = crossAllR;
        out<<R<<','<<X<<','<<mertensAtX[R]<<','<<smallM[R-1]<<','<<Q<<','<<K<<','<<C<<','<<A<<','<<nonzero<<','<<positive<<','<<negative<<','<<px<<','<<-signedB<<','<<absB<<','<<plusB<<','<<minusB<<','<<(absB?double(signedB)/absB:0)<<','<<muAvg<<','<<indB<<','<<corr<<','<<smooth<<','<<(positive&&negative?double(minGap)/(positive*negative):0)<<','<<(positive&&negative?double(maxGap)/(positive*negative):0)<<','<<(seenP&&seenN?1:0)<<','<<colsum<<','<<colnormAll<<','<<crossAll<<','<<cross1All<<','<<crossSharedAll<<','<<unsigned1All<<','<<(unsignedAllR-unsigned1All)<<','<<(colsum*colsum-colnormAll)<<'\n';
        if(R%1000==0)cerr<<"Processed R="<<R<<"\n";
    }
    cerr<<"PASS: all cofactor scans and selected owners reconstructed exactly.\n";
}
