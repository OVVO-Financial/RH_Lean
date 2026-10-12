// Genuine Möbius prime-dilation pair-density and dependence audit.
// Compile: g++ -O3 -std=c++17 -Wall -Wextra -Werror
//   experiments/PrimePopulationCutoff/mobius_prime_dilation_density.cpp -o /tmp/mobius_dilation
// Run: /tmp/mobius_dilation 500000
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;

int main(int argc, char** argv) {
  int N = argc > 1 ? stoi(argv[1]) : 500000;
  if (N < 1 || N > 1000000) return 2;
  const vector<int> shifts = {2, 3, 5, 6, 30};
  int mx = N * 30;
  vector<int> lp(mx + 1), primes;
  vector<int8_t> mu(mx + 1);
  mu[1] = 1;
  for (int n = 2; n <= mx; ++n) {
    if (!lp[n]) {lp[n] = n; mu[n] = -1; primes.push_back(n);}
    for (int p : primes) {
      int64_t v = static_cast<int64_t>(n) * p;
      if (v > mx || p > lp[n]) break;
      lp[v] = p;
      if (n % p == 0) {mu[v] = 0; break;}
      mu[v] = -mu[n];
    }
  }
  const double pi = acos(-1.0), d0 = 6.0 / (pi * pi);
  cout << fixed << setprecision(9);
  cout << "N,k,mu(k),actual_mask_count,expected_mask_count,"
          "signed_pair_sum,expected_signed_pair_sum,raw_pearson,theoretical_pearson,mask_error,zero_sign_errors\n";
  for (int k : shifts) {
    int x = k;
    double rho = d0;
    for (int p : primes) {
      if (p > x) break;
      if (x % p == 0) {
        rho *= static_cast<double>(p) / (p + 1);
        while (x % p == 0) x /= p;
      }
    }
    int64_t sumA = 0, sumB = 0, sumAA = 0, sumBB = 0;
    int64_t sumAB = 0, mask = 0;
    int errors = 0;
    for (int n = 1; n <= N; ++n) {
      const int a = mu[n], b = mu[k * n];
      const int f = a * (std::gcd(n,k) == 1);
      if (b != static_cast<int>(mu[k]) * f) ++errors;
      sumA += a; sumB += b; sumAA += a * a;
      sumBB += b * b; sumAB += a * b;
      mask += (a != 0 && std::gcd(n,k) == 1);
    }
    const double cov = static_cast<double>(sumAB) / N -
      static_cast<double>(sumA) * sumB / (static_cast<double>(N) * N);
    const double varA = static_cast<double>(sumAA)/N -
      pow(static_cast<double>(sumA)/N,2);
    const double varB = static_cast<double>(sumBB)/N -
      pow(static_cast<double>(sumB)/N,2);
    const double correlation = cov / sqrt(varA * varB);
    cout << N << ',' << k << ',' << static_cast<int>(mu[k]) << ','
         << mask << ',' << rho * N << ',' << sumAB << ','
         << static_cast<int>(mu[k]) * rho * N << ',' << correlation << ','
         << static_cast<int>(mu[k]) * sqrt(rho/d0) << ','
         << (mask - rho*N) << ',' << errors << '\n';
  }
  return 0;
}
