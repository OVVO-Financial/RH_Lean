// Independent 100-million-integer finite prime/factor audit; NOT a RH proof.
// Exact integer sieve; gcd-30 candidate population; double VF midpoint mass.
// Compile: c++ -O3 -std=c++17 -o /tmp/vf-factor30 verify_cpp.cpp
// Run: /tmp/vf-factor30 10000
#include <cassert>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <string>
#include <vector>

int main(int argc, char **argv) {
  const std::uint64_t R = argc > 1 ? std::stoull(argv[1]) : 10000ULL;
  if (R < 1027 || R > 10000) return 2;
  const std::uint64_t limit = (R + 1) * (R + 1);
  std::vector<std::uint8_t> composite(limit + 1, 0);
  composite[0] = composite[1] = 1;
  for (std::uint64_t p = 2; p*p <= limit; ++p)
    if (!composite[p])
      for (std::uint64_t j = p*p; j <= limit; j += p)
        composite[j] = 1;

  std::vector<double> F(R + 2, 0.0);
  for (std::uint64_t r = 2; r <= R; ++r)
    F[r + 1] = F[r] + (2.0*r + 1.0) / std::log((double)r*r+r+0.5);
  const double sqrt2 = std::sqrt(2.0);
  std::uint64_t pi = 9, candidates = 0, covered = 0, prime = 0, removed5 = 0;
  std::uint64_t firstFailure = 0, minMarginAt = 0, normAt = 0, slackAt = 0;
  long double totalExcess = 0, maxTelescope = 0, maxNorm = 0;
  long double minMargin = 1e300L, minSlack = 1e300L;
  for (std::uint64_t r = 5; r <= R; ++r) {
    const double defect = (double)pi-F[r];
    maxTelescope = std::max(maxTelescope,
      fabsl(((long double)9-F[5]-totalExcess)-defect));
    const double norm = std::fabs(defect)/(r*std::log((double)r));
    if (norm > maxNorm) {maxNorm = norm; normAt = r;}
    const double slack = defect+2*r*std::log((double)r);
    if (slack < minSlack) {minSlack = slack; slackAt = r;}
    const auto lag = (std::uint64_t)std::min((double)(r/2),
      std::floor(0.4*std::pow(std::log((double)r),2)));
    const auto level = (std::uint64_t)std::floor(F[r-lag]+sqrt2);
    const double margin = (double)pi-(double)level;
    if (margin < minMargin) {minMargin = margin; minMarginAt = r;}
    if (margin < 0 && firstFailure == 0) firstFailure = r;

    std::uint64_t N = 0, C = 0, P = 0, M = 0;
    for (std::uint64_t n = r*r+1; n < (r+1)*(r+1); ++n) {
      if (n%10 == 5) ++M;
      if (n%2 && n%3 && n%5) {
        ++N;
        if (composite[n]) ++C; else ++P;
      } else if (!composite[n]) {std::cerr << "Noncomposite excluded: " << n; return 3;}
    }
    assert(N == P+C);
    totalExcess += (long double)C - ((long double)N - (F[r+1]-F[r]));
    pi += P; candidates += N; covered += C; prime += P; removed5 += M;
  }
  auto g = [](std::uint64_t t) {
    std::uint64_t x=0; for (std::uint64_t i=1;i<=t;++i)
      if(i%2&&i%3&&i%5)++x; return x;
  };
  auto prefix30 = [&](std::uint64_t n){return 8*(n/30)+g(n%30);};
  const std::uint64_t A=5, B=R+1;
  const auto physical=prefix30(B*B)-prefix30(A*A)-prefix30(B)+prefix30(A);
  assert(physical == candidates);
  const long double predicted=(4.0L/15.0L)*((long double)(B*B-A*A)-(B-A));
  const auto phase=(long double)physical-predicted;
  assert(fabsl(phase) <= (32.0L/15.0L)+1e-8);
  std::cout << std::fixed << std::setprecision(12)
    << "{\"status\":\"finite_exact_factor_sieve_not_RH\","
    << "\"max_root\":" << R << ",\"blocks\":" << R-4
    << ",\"candidates\":" << candidates
    << ",\"covered\":" << covered
    << ",\"survivors\":" << prime
    << ",\"ending_5\":" << removed5
    << ",\"sqrt2_first_horizontal_failure\":" << firstFailure
    << ",\"smallest_horizontal_margin\":" << (double)minMargin
    << ",\"smallest_horizontal_margin_R\":" << minMarginAt
    << ",\"min_lower_K2_slack\":" << (double)minSlack
    << ",\"min_lower_K2_slack_R\":" << slackAt
    << ",\"largest_normalized_defect\":" << (double)maxNorm
    << ",\"largest_normalized_defect_R\":" << normAt
    << ",\"max_telescoping_rounding\":" << (double)maxTelescope
    << ",\"wheel30_endpoint_phase\":" << (double)phase << "}" << std::endl;
  return 0;
}
