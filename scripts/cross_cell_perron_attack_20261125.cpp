#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <vector>
using namespace std;using ld=long double;
struct Energy{ld diag=0;size_t n=0;void add(ld x){diag+=x*x;n++;}};
void run(int R){
 const uint32_t X=uint32_t(uint64_t(R)*R-1),Y=uint32_t(uint64_t(2*R)*(2*R)-1);const ld t=ld(X)/Y;
 vector<uint32_t> sp(size_t(Y)+1),pr;pr.reserve(Y/10);
 for(uint32_t n=2;n<=Y;++n){if(!sp[n]){sp[n]=n;pr.push_back(n);}for(uint32_t p:pr){uint64_t d=uint64_t(n)*p;if(d>Y||p>sp[n])break;sp[d]=p;}}
 vector<ld> V(2*R,1);for(int r=2;r<2*R;r++){V[r]=V[r-1];if(sp[r]==uint32_t(r))V[r]*=(1-1/ld(r));}
 int j=floor(log2(R));uint32_t b=pr.at(j-1),c=cbrtl(Y);while(uint64_t(c+1)*(c+1)*(c+1)<=Y)++c;while(uint64_t(c)*c*c>Y)--c;assert(b<c&&uint64_t(b)*b<=X);
 auto g=[&](uint32_t n)->ld{return n<=X?1-t:ld(X)/n-t;};auto hw=[&](uint32_t n)->ld{return logl(n)*g(n);};
 auto rt=[](uint32_t n){uint32_t r=sqrt(double(n));while(uint64_t(r+1)*(r+1)<=n)++r;while(uint64_t(r)*r>n)--r;return r;};
 auto d=[&](uint32_t n,uint32_t r,uint32_t cut)->ld{if(r<=cut||sp[n]<=cut)return 0;return V[r]/V[cut]-(sp[n]==n?1:0);};
 // Independent top-band root enumeration (including prime squares).
 vector<uint8_t> positiveRoot(size_t(Y/c)+2,0);uint64_t posPairs=0,posRoots=0,negRoots=0,overlap=0;ld rootPos=0,rootNeg=0;
 for(size_t i=upper_bound(pr.begin(),pr.end(),c)-pr.begin();i<pr.size();i++){uint32_t p=pr[i];if(uint64_t(p)*p>Y)break;for(size_t k=i;k<pr.size();k++){uint32_t q=pr[k];uint64_t n=uint64_t(p)*q;if(n>Y)break;assert(q<positiveRoot.size());if(!positiveRoot[q]){positiveRoot[q]=1;++posRoots;}++posPairs;rootPos+=V[rt(n)]/V[c]*hw(n);}}
 for(uint32_t q:pr){uint32_t r=rt(q);if(r<=c)continue;ld z=1-V[r]/V[c];if(z==0)continue;rootNeg+=z*hw(q);++negRoots;if(q<positiveRoot.size()&&positiveRoot[q])++overlap;}
 ld highPos=0,highNeg=0,topPos=0,topNeg=0,base=0,high=0,low=0,prime=0,center=0,cellTotal=0,freezeTotal=0,freezeAbs=0,cellDiag=0,baseDiag=0,debtDiag=0,baseDebt=0;
 ld isolatedTop=0,frozenHigh=0;uint64_t isolatedCount=0,shiftCount=0;vector<ld> shiftErr(2*R,0),prefixBefore(2*R,0);vector<uint64_t> lastVirtual(2*R,UINT64_MAX);vector<unsigned> hitsVirtual(2*R,0);unsigned maxVirtual=0;ld cellWeightSum=0;uint64_t topPosCount=0,topNegCount=0,cutChecks=0;uint32_t r=1;ld ec=0,bc=0,dc=0,uc=0;unsigned num=0;uint32_t anchor=2;
 const array<uint32_t,8> sizes={1,4,16,64,256,1024,4096,16384};array<Energy,8> en;array<ld,8> buf{};uint64_t cells=0;
 auto finish=[&](){if(!num)return;const ld frozen=hw(anchor)*uc-g(anchor)*num;cellTotal+=ec;freezeTotal+=frozen;freezeAbs+=fabsl(ec-frozen);cellDiag+=ec*ec;baseDiag+=bc*bc;debtDiag+=dc*dc;baseDebt+=bc*dc;cells++;for(size_t a=0;a<sizes.size();a++){buf[a]+=ec;if(cells%sizes[a]==0){en[a].add(buf[a]);buf[a]=0;}}ec=bc=dc=uc=0;num=0;};
 for(uint32_t n=2;n<=Y;++n){while(uint64_t(r+1)*(r+1)<=n)++r;ld h=hw(n),z=g(n),dh=d(n,r,b),dt=d(n,r,c);ld all=V[r]-(sp[n]==n?1:0),dl=all-dh,u=V[r]-dh;
 assert(fabsl(u)<=1+1e-16L);++cutChecks;if(dh>0)highPos+=dh*h;else highNeg-=dh*h;if(dt>0){assert(sp[n]>c&&sp[n]!=n&&sp[n/sp[n]]==n/sp[n]);topPos+=dt*h;++topPosCount;}else if(dt<0){topNeg-=dt*h;++topNegCount;}
 if(n>Y/2&&uint64_t(4)*n<=uint64_t(3)*Y&&dt<0){isolatedTop-=dt*h;++isolatedCount;}
 uint32_t cell=(n-1)/4,first=4*cell+1;frozenHigh+=dh*hw(first);
 if(n%4==1){if(uint64_t(r)*r==n&&sp[r]==r)prefixBefore[r]=cellWeightSum;cellWeightSum+=V[r]*h;}
 if(sp[n]>b&&sp[n]<n&&sp[n]<=r){uint32_t p=sp[n],m=n/p;uint64_t k2=uint64_t(p)*((m-1)/4+1)-1;assert(k2>=cell&&k2-cell<p&&(m%4==1||m%4==3));if(lastVirtual[p]!=k2){if(lastVirtual[p]!=UINT64_MAX)assert(lastVirtual[p]<cell);lastVirtual[p]=k2;hitsVirtual[p]=0;}maxVirtual=max(maxVirtual,++hitsVirtual[p]);assert(hitsVirtual[p]<=2);ld aold=V[r]/V[p],anew=0;uint64_t n2=4*k2+1;if(n2<=Y)anew=V[rt(n2)]/V[p]*hw(n2);shiftErr[p]+=anew-aold*hw(first);++shiftCount;}
 base+=V[r]*h;high+=dh*h;low+=dl*h;if(sp[n]==n)prime+=h;center+=z;if(!num)anchor=n;ec+=u*h-z;bc+=V[r]*h-z;dc+=dh*h;uc+=u;++num;if(n%4==0||n==Y)finish();}
 for(size_t a=0;a<sizes.size();a++)if(cells%sizes[a])en[a].add(buf[a]);ld exactCenter=ld(X)*logl(ld(Y)/X),I=prime-exactCenter,Ihigh=base-high-exactCenter;
 ld shiftNet=0,shiftAbs=0,shiftMax=0,shiftBound=0,sawNet=0,sawAbs=0,sawBound=0;uint32_t np=0;for(uint32_t p:pr){if(p<=b||p>=2*R)continue;shiftNet+=shiftErr[p];shiftAbs+=fabsl(shiftErr[p]);shiftMax=max(shiftMax,fabsl(shiftErr[p]));shiftBound+=2*hw(X);++np;assert(fabsl(shiftErr[p])<=2*hw(X)+1e-7L);
 uint64_t k0=(uint64_t(p)*p-1)/4,K=uint64_t(R)*R;ld msum=0;for(uint64_t k1=((k0+p)/p)*p;k1<=K;k1+=p){uint32_t n=4*(k1-1)+1;msum+=V[rt(n)]*hw(n);}ld saw=4*ld(p)/(p-1)*(msum-(cellWeightSum-prefixBefore[p])/p);sawNet+=saw;sawAbs+=fabsl(saw);ld sb=4*V[p-1]*hw(X);sawBound+=sb;assert(fabsl(saw)<=sb+1e-7L);}assert(fabsl(frozenHigh-high)<=12*hw(X)+1e-7L);
 auto near=[&](ld a,ld z){assert(fabsl(a-z)<1e-9L*max({ld(1),fabsl(a),fabsl(z)}));};
 uint64_t directCellChecks=0;ld directDiscrepancy=0; if(R<=317){uint32_t K=R*R;vector<uint32_t> F(K+1);for(uint32_t p:pr){if(p<=b||p>=2*R)continue;auto old=[&](uint32_t n){return n==1||sp[n]>=p;};F[0]=0;for(uint32_t k=0;k<K;k++)F[k+1]=F[k]+old(4*k+1)+old(4*k+3);uint32_t removed=0,k0=(p*p-1)/4;auto E=[&](uint32_t k)->ld{return ld(F[k])-4*V[p-1]*k;};auto G=[&](uint32_t k)->ld{return E(k/p)-E(k)/p;};for(uint32_t k=0;k<K;k++){uint32_t n=4*k+1;removed+=(old(n)&&n%p==0)+(old(n+2)&&((n+2)%p==0));uint32_t m=(4*(k+1))/p,jj=(k+1)/p,partial=0;for(uint32_t v=4*jj+1;v<=m;v++)partial+=old(v);assert(partial<=2&&removed==F[jj]+partial);++directCellChecks;if(k>=k0)directDiscrepancy+=(V[rt(n)]/V[p])*hw(n)*(G(k+1)-G(k));}}near(directDiscrepancy,frozenHigh+shiftNet-sawNet);}
near(rootPos,topPos);near(rootNeg,topNeg);assert(posPairs==topPosCount&&negRoots==topNegCount&&overlap==0);near(Ihigh,I+low);near(cellTotal,Ihigh+exactCenter-center);near(cellDiag,baseDiag+debtDiag-2*baseDebt);near(high,highPos-highNeg);assert(freezeAbs<=6*logl(X)+3+1e-8L);assert(exactCenter-center>=-1e-7L&&exactCenter-center<=2.0000001L);
 cout<<setprecision(14)<<"{\"R\":"<<R<<",\"X\":"<<X<<",\"Y\":"<<Y<<",\"low_cut\":"<<b<<",\"cube_cut\":"<<c<<",\"sites\":"<<cutChecks<<",\"cells\":"<<cells<<",\"I\":"<<I<<",\"I_high\":"<<Ihigh<<",\"low_increment\":"<<low<<",\"quadrature\":"<<exactCenter-center<<",\"freeze_error\":"<<freezeTotal-cellTotal<<",\"freeze_abs\":"<<freezeAbs<<",\"freeze_bound\":"<<6*logl(X)+3<<",\"cell_total\":"<<cellTotal<<",\"cell_diag\":"<<cellDiag<<",\"base_diag\":"<<baseDiag<<",\"debt_diag\":"<<debtDiag<<",\"base_debt_cross\":"<<baseDebt<<",\"high_pos\":"<<highPos<<",\"high_neg\":"<<highNeg<<",\"top_pos\":"<<topPos<<",\"top_neg\":"<<topNeg<<",\"top_pos_pairs\":"<<posPairs<<",\"top_pos_roots\":"<<posRoots<<",\"top_neg_roots\":"<<negRoots<<",\"top_root_overlap\":"<<overlap<<",\"isolated_top_mass\":"<<isolatedTop<<",\"isolated_count\":"<<isolatedCount<<",\"shift_count\":"<<shiftCount<<",\"high_prime_count\":"<<np<<",\"frozen_high_error\":"<<frozenHigh-high<<",\"shift_net\":"<<shiftNet<<",\"shift_abs\":"<<shiftAbs<<",\"shift_max\":"<<shiftMax<<",\"shift_bound\":"<<shiftBound<<",\"rounded_high\":"<<frozenHigh+shiftNet<<",\"max_virtual_cell_occupancy\":"<<maxVirtual<<",\"saw_net\":"<<sawNet<<",\"saw_abs\":"<<sawAbs<<",\"saw_bound\":"<<sawBound<<",\"discrepancy_high\":"<<frozenHigh+shiftNet-sawNet<<",\"direct_cell_checks\":"<<directCellChecks<<",\"direct_discrepancy\":"<<directDiscrepancy<<",\"energies\":[";for(size_t a=0;a<sizes.size();a++){if(a)cout<<",";cout<<"{\"width\":"<<sizes[a]<<",\"groups\":"<<en[a].n<<",\"energy\":"<<en[a].diag<<"}";}cout<<"]}"<<endl;
}
int main(int argc,char**argv){if(argc==1)for(int r:{64,317,1027,2048,4096})run(r);else for(int i=1;i<argc;i++)run(atoi(argv[i]));}
