// Actual (not randomized) Mobius square endpoint census for all 2<=R<=MAX_R.
// Compile: g++ -O3 -std=c++17 mobius_root_census.cpp -o mobius_root_census
// Run: ./mobius_root_census 6000 actual_root_scan.csv
#include <vector>
#include <cstdint>
#include <iostream>
#include <fstream>
#include <cmath>
#include <iomanip>
#include <cstdlib>
using namespace std;
int main(int argc,char**argv){
    const int Rmax=argc>1?atoi(argv[1]):6000;
    if(Rmax<2 || Rmax>12000){cerr<<"Rmax must be [2,12000]\n";return 2;}
    const int64_t N=1LL*Rmax*Rmax-1;
    vector<uint8_t> composite(N+1,0);
    vector<int8_t> mu(N+1,1);
    mu[0]=0;
    for(int64_t p=2;p<=N;p++){
        if(composite[p])continue;
        if(p*p<=N){for(int64_t n=p*p;n<=N;n+=p)composite[n]=1;}
        for(int64_t n=p;n<=N;n+=p)mu[n]=-mu[n];
        if(p*p<=N)for(int64_t n=p*p;n<=N;n+=p*p)mu[n]=0;
    }
    vector<int> hist(Rmax+1,0),Mx(Rmax+1,0);
    int64_t M=0;
    int r=2;
    for(int64_t n=1;n<=N;n++){
        M+=mu[n];
        if(n<=Rmax)hist[n]=(int)M;
        if(r<=Rmax && n==1LL*r*r-1){Mx[r]=(int)M;r++;}
    }
    if(r!=Rmax+1){cerr<<"Failure all roots not filled\n";return 3;}
    const int ps[]={2,3,5,7,11,13,17,19,23,29};
    double K=1;
    ofstream out(argc>2?argv[2]:"actual_root_scan.csv");
    out<<"R,M_X,M_R_minus_1,Q_R,K_R,C_R,A_R,sine_y\n";
    out<<setprecision(15);
    for(int R=2;R<=Rmax;R++){
        const int y=R-1;
        const double histdelta=hist[y]-1.;
        K=max(K,histdelta*histdelta/(y+1.));
        const int Q=2*hist[R-1]-Mx[R];
        const double C=abs(double(Q))/(R*sqrt(K));
        const double A=(Mx[R]-1.)*(Mx[R]-1.)/(double(R)*R*K);
        int64_t X=1LL*R*R-1;
        double sum=0.;
        for(int p:ps){int residue=int(X%p); if(p!=2)sum+=sin((2.*acos(-1.))*residue/p);}
        out<<R<<","<<Mx[R]<<","<<hist[R-1]<<","<<Q<<","<<K<<","<<C<<","<<A<<","<<sum<<"\n";
    }
    cout<<"sieved n<="<<N<<" and all roots R<= "<<Rmax<<"; M(N)="<<M<<" output complete\n";
    for(int q: {56,317,1000,5561,6000})if(q<=Rmax)
        cout<<"R="<<q<<" M(R^2-1)="<<Mx[q]<<" M(R-1)="<<hist[q-1]<<"\n";
}
