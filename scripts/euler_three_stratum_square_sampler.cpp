// Exact, integer-only three-stratum Euler prime population and dyadic sampler.
// Reuse the independently tested original Mobius/prime-count sieve implementation.
// No random signs, model distributions, fitted exponents or Li surrogates.
#define main baseline_admissible_euler_probe_main
#include "euler_admissible_population_probe.cpp"
#undef main

#include <array>

struct Three {
  int64_t low;
  int64_t middle; // signed composite response, can be positive or negative
  int64_t top;    // negative count of primes in (X/2,X]
  int64_t mertens;
};

struct SixMoment {
  int64_t ll=0, mm=0, tt=0, lm=0, lt=0, mt=0, total=0;
};

Three three_at(int root, const Sieve &s) {
  const int x = root * root - 1;
  const int lower = root - 1;
  const int64_t top = -static_cast<int64_t>(s.pi[x]-s.pi[x/2]);
  int64_t middle_debt = 0;
  for (int k=2; k<root; ++k) {
    int left = std::max(lower, x/(k+1));
    int right = x/k;
    assert(left<=right);
    const int64_t count = static_cast<int64_t>(s.pi[right]-s.pi[left]);
    middle_debt += s.mertens[k]*count;
  }
  const int64_t middle = -middle_debt;
  const int64_t mertens = s.mertens[x];
  const int64_t low = mertens-middle-top;
  assert(low+middle+top==mertens);
  return {low,middle,top,mertens};
}

void independent_at(int root, const Sieve &s, const Three &v) {
  const int x=root*root-1;
  int64_t direct_low=0, direct_middle_debt=0;
  for (int n=1;n<=x;++n)
    if (s.largest[n] < static_cast<uint32_t>(root)) direct_low+=s.mu[n];
  for (int p:s.primes) {
    if (p<x/2+1 && p>=root) direct_middle_debt += s.mertens[x/p];
    if (p>x/2) break;
  }
  const auto prime_begin=std::upper_bound(s.primes.begin(),s.primes.end(),x/2);
  const auto prime_end=std::upper_bound(s.primes.begin(),s.primes.end(),x);
  const auto direct_top=-(prime_end-prime_begin);
  assert(v.low==direct_low);
  assert(v.middle==-direct_middle_debt);
  assert(v.top==direct_top);
  std::cout<<"R="<<root<<" X="<<x<<" low="<<v.low
     <<" middle="<<v.middle<<" top="<<v.top
     <<" M(X)="<<v.mertens<<"\n";
}


// The moving half-wall contribution is deterministic reclassification;
// the cofactor-shell response below is the *genuine* signed prime/composite
// incidence that remains after that reclassification cancels.
struct SignedThreeFlow {
  int64_t prime_births=0;       // primes newly crossing upper square wall
  int64_t half_gate=0;          // primes crossing moving X/2 wall
  int64_t composite_shell=0;    // sum_c mu(c) * actual prime hits with cp in shell
  int64_t root_gate=0;          // root R admission: 1_{R prime} M(R-1)
};

SignedThreeFlow three_flow(int root,const Sieve &s) {
  const int x=root*root-1;
  const int y=(root+1)*(root+1)-1;
  SignedThreeFlow v;
  v.prime_births=static_cast<int64_t>(s.pi[y])-s.pi[x];
  v.half_gate=static_cast<int64_t>(s.pi[y/2])-s.pi[x/2];
  v.root_gate=
      (s.least[root]==static_cast<uint32_t>(root)) ? s.mertens[root-1] : 0;
  for (int cof=2;cof<=root;++cof) {
    const int left=std::max(root,x/cof);
    const int right=y/cof;
    assert(left<=right);
    const int64_t n=static_cast<int64_t>(s.pi[right])-s.pi[left];
    // The displayed child products all obey R^2<=cof*p<=(R+1)^2-1,
    // p>R, and cof<=R, so gcd(p,cof)=1 automatically.
    v.composite_shell+=s.mu[cof]*n;
  }
  return v;
}

struct MixedDissection {
  int64_t transfer_component=0, composite_component=0, root_component=0;
  int64_t total=0;
};

MixedDissection dissection(const std::vector<Three> &v,
                           const Sieve &s,int H) {
  MixedDissection out;
  for (int root=H;root<2*H;++root) {
    SignedThreeFlow t=three_flow(root,s);
    const int64_t dm=v[root+1].middle-v[root].middle;
    const int64_t du=v[root+1].top-v[root].top;
    const int64_t db=t.prime_births-t.half_gate;
    assert(du==-db);
    assert(dm==t.root_gate-t.half_gate-t.composite_shell);
    assert(dm+du==t.root_gate-t.composite_shell-t.prime_births);
    out.transfer_component+=2*t.half_gate*db;
    out.composite_component+=2*t.composite_shell*db;
    out.root_component-=2*t.root_gate*db;
    out.total+=2*dm*du;
  }
  assert(out.transfer_component+out.composite_component+
         out.root_component==out.total);
  return out;
}


// Cross the three moving prime-factor admission bands with the three
// literal INTEGER-SITE intervals [1,R-1], [R,X/2], (X/2,X].
// There are six (not nine) potentially nonempty cells. The composite and
// singleton terms remain together in the middle prime-factor band.
using SixCells = std::array<int64_t,6>;
SixCells two_axis_at(int root,const Sieve &s,const Three &v) {
  const int x=root*root-1, y=x/2;
  int64_t debt_y=0;
  for(int k=1;k<=y/root;++k) {
    const int left=std::max(root-1,y/(k+1)),right=y/k;
    assert(left<=right);
    debt_y+=s.mertens[k]*
      (static_cast<int64_t>(s.pi[right])-s.pi[left]);
  }
  const int64_t smooth_y=static_cast<int64_t>(s.mertens[y])+debt_y;
  SixCells a{{
    s.mertens[root-1], smooth_y-s.mertens[root-1], -debt_y,
    v.low-smooth_y, v.middle+debt_y, v.top
  }};
  int64_t total=0;
  for(auto k:a) total+=k;
  assert(total==v.mertens);
  assert(a[0]+a[1]+a[3]==v.low);
  assert(a[2]+a[4]==v.middle);
  assert(a[5]==v.top);
  return a;
}

struct NestedMoment {
  int64_t site_diag=0,site_cross=0,six_diag=0,six_cross=0;
  int64_t squarefree_diag=0;
  double null_sd=0;
};

NestedMoment nested_window(const std::vector<SixCells> &a,
                           const std::vector<Three> &v,
                           const Sieve &s,int H) {
  NestedMoment out;
  double null_var=0;
  int64_t observed=0;
  for(int R=H;R<2*H;++R) {
    SixCells d{};
    int64_t z=0;
    for(int j=0;j<6;++j) {
      d[j]=a[R+1][j]-a[R][j];
      out.six_diag+=d[j]*d[j];
      z+=d[j];
    }
    out.six_cross+=z*z;
    for(int j=0;j<6;++j) out.six_cross-=d[j]*d[j];
    const std::array<int64_t,3> site{{
      d[0],d[1]+d[2],d[3]+d[4]+d[5]
    }};
    for(const auto x:site) out.site_diag+=x*x;
    out.site_cross+=z*z;
    for(const auto x:site) out.site_cross-=x*x;
    const int64_t physical=v[R+1].mertens-v[R].mertens;
    assert(z==physical);
    observed+=z*z;
    int64_t squarefree=0;
    for(int n=R*R;n<(R+1)*(R+1);++n)
      squarefree+=s.mu[n]*s.mu[n];
    out.squarefree_diag+=squarefree;
    null_var+=2.0*squarefree*(squarefree-1);
  }
  assert(out.site_diag+out.site_cross==observed);
  assert(out.six_diag+out.six_cross==observed);
  out.null_sd=std::sqrt(null_var);
  return out;
}

SixMoment window(const std::vector<Three> &v,int H) {
  SixMoment s;
  for (int r=H; r<2*H; ++r) {
    const int64_t a=v[r+1].low-v[r].low;
    const int64_t b=v[r+1].middle-v[r].middle;
    const int64_t c=v[r+1].top-v[r].top;
    const int64_t d=v[r+1].mertens-v[r].mertens;
    assert(a+b+c==d);
    s.ll+=a*a;
    s.mm+=b*b;
    s.tt+=c*c;
    s.lm+=2*a*b;
    s.lt+=2*a*c;
    s.mt+=2*b*c;
    s.total+=d*d;
  }
  assert(s.ll+s.mm+s.tt+s.lm+s.lt+s.mt==s.total);
  return s;
}

int main() {
  constexpr int maxR=10000;
  Sieve s(maxR*maxR-1);
  std::vector<Three> values(maxR+1);
  std::vector<SixCells> cells(maxR+1);
  int sign_positive=0,sign_zero=0,sign_negative=0;
  for (int root=2;root<=maxR;++root) {
    values[root]=three_at(root,s);
    cells[root]=two_axis_at(root,s,values[root]);
    if (values[root].middle>0) ++sign_positive;
    else if (values[root].middle<0) ++sign_negative;
    else ++sign_zero;
    if (root==317||root==1027||root==5561||root==10000)
      independent_at(root,s,values[root]);
  }
  std::cout<<"ALL ROOTS 2.."<<maxR
    <<" middle positive="<<sign_positive
    <<" middle negative="<<sign_negative
    <<" middle zero="<<sign_zero<<"\n";

  for (int H : std::array<int,5>{{16,64,256,1024,4096}}) {
    SixMoment m=window(values,H);
    const NestedMoment nested=nested_window(cells,values,s,H);
    const MixedDissection d=dissection(values,s,H);
    assert(d.total==m.mt);
    const int64_t diagonals=m.ll+m.mm+m.tt;
    const int64_t crosses=m.lm+m.lt+m.mt;
    std::cout<<"H="<<H<<" shellEnergy="<<m.total
      <<" diagonalThree="<<diagonals
      <<" crossThree="<<crosses
      <<" LL="<<m.ll<<" MM="<<m.mm<<" TT="<<m.tt
      <<" 2LM="<<m.lm<<" 2LT="<<m.lt<<" 2MT="<<m.mt
      <<" MT_halfGate="<<d.transfer_component
      <<" MT_composites="<<d.composite_component
      <<" MT_rootGate="<<d.root_component
      <<" squarefreeDiag="<<nested.squarefree_diag
      <<" actualToRandom="<<(double(m.total)/nested.squarefree_diag)
      <<" nullReferenceZ="<<((m.total-nested.squarefree_diag)/nested.null_sd)
      <<" siteDiag="<<nested.site_diag
      <<" siteCross="<<nested.site_cross
      <<" sixCellDiag="<<nested.six_diag
      <<" sixCellCross="<<nested.six_cross<<"\n";
  }
  std::cout<<"PASS independent three-stratum prime-product population,"
    <<" top prime singleton, six-moment square-block sampler\n";
}
