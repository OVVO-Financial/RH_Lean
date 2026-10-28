// Two successive deterministic sampling filters: moving integer site interval
// and largest-admitted-prime Euler class, observed with R uniform in [H,2H).
// Exact integer Mobius values throughout; no randomized signs or fitted model.
#define main prime_owner_three_stratum_main
#include "euler_three_stratum_square_sampler.cpp"
#undef main
#include <array>

struct Site3 {
  int64_t low=0, middle=0, top=0, all=0;
};

Site3 site_at(int r, const Sieve &s) {
  const int x=r*r-1;
  const int b=x/2;
  const int64_t low=s.mertens[r-1];
  const int64_t middle=s.mertens[b]-low;
  const int64_t top=s.mertens[x]-s.mertens[b];
  const int64_t all=s.mertens[x];
  assert(low+middle+top==all);
  return {low,middle,top,all};
}

void audit_actual_site_owner_cells(int r,const Sieve &s,
                                   const Site3 &site,const Three &owner) {
  const int x=r*r-1,b=x/2;
  int64_t cell[3][3]={{0}};
  for(int n=1;n<=x;++n) {
    if(s.mu[n]==0)continue;
    int row=n<r?0:(n<=b?1:2);
    int owner_p=static_cast<int>(s.largest[n]);
    int col=owner_p<r?0:(owner_p<=b?1:2);
    cell[row][col]+=s.mu[n];
    if(row==0)assert(col==0);
    if(col==2) {
      assert(row==2);
      assert(owner_p==n && s.mu[n]==-1);
    }
  }
  assert(cell[0][0]+cell[0][1]+cell[0][2]==site.low);
  assert(cell[1][0]+cell[1][1]+cell[1][2]==site.middle);
  assert(cell[2][0]+cell[2][1]+cell[2][2]==site.top);
  assert(cell[0][0]+cell[1][0]+cell[2][0]==owner.low);
  assert(cell[0][1]+cell[1][1]+cell[2][1]==owner.middle);
  assert(cell[0][2]+cell[1][2]+cell[2][2]==owner.top);
  int64_t total=0;
  for(const auto &row:cell)for(const auto v:row) total+=v;
  assert(total==site.all);
  std::cout<<"R="<<r<<" physical-site rows and prime-owner columns\n";
  for(int i=0;i<3;++i) {
    std::cout<<"  site"<<i<<":";
    for(int j=0;j<3;++j)std::cout<<" "<<cell[i][j];
    std::cout<<"\n";
  }
}

struct Nine {
  int64_t m[3][3]={{0}};
  int64_t energy=0;
};

Nine dyadic_two_axis(int H,const std::vector<Site3>& site,
                     const std::vector<Three>& owner) {
  Nine out;
  for(int r=H;r<2*H;++r) {
    const std::array<int64_t,3> a = {
      site[r+1].low-site[r].low,
      site[r+1].middle-site[r].middle,
      site[r+1].top-site[r].top
    };
    const std::array<int64_t,3> b = {
      owner[r+1].low-owner[r].low,
      owner[r+1].middle-owner[r].middle,
      owner[r+1].top-owner[r].top
    };
    const int64_t d=owner[r+1].mertens-owner[r].mertens;
    assert(a[0]+a[1]+a[2]==d);
    assert(b[0]+b[1]+b[2]==d);
    for(int i=0;i<3;++i)for(int j=0;j<3;++j)
      out.m[i][j]+=a[i]*b[j];
    out.energy+=d*d;
  }
  int64_t cross=0;
  for(const auto &row:out.m)for(const auto v:row)cross+=v;
  assert(cross==out.energy);
  return out;
}

int main() {
  constexpr int maxR=10000;
  Sieve sieve(maxR*maxR-1);
  std::vector<Site3> sites(maxR+1);
  std::vector<Three> owners(maxR+1);
  for(int r=2;r<=maxR;++r) {
    sites[r]=site_at(r,sieve);
    owners[r]=three_at(r,sieve);
    assert(sites[r].all==owners[r].mertens);
    if(r==317 || r==1027 || r==5561 || r==10000)
      audit_actual_site_owner_cells(r,sieve,sites[r],owners[r]);
  }
  for(int H : std::array<int,5>{{16,64,256,1024,4096}}) {
    Nine v=dyadic_two_axis(H,sites,owners);
    std::cout<<"H="<<H<<" shellEnergy="<<v.energy
      <<" fullNineCross="<<v.energy<<"\n";
    for(int i=0;i<3;++i) {
      std::cout<<"  siteChange"<<i<<" x ownerChange[0,1,2]:";
      for(int j=0;j<3;++j)std::cout<<" "<<v.m[i][j];
      std::cout<<"\n";
    }
  }
  std::cout<<"PASS two-axis stratified sampling with actual Mobius,"
           " actual prime-owner cross cells, and all nine signed dyadic moments\n";
}
