# Exact finite-prefix extension experiment

These programs are finite computation, not an infinite Mertens envelope proof.

## Reproduce the interval certificates and two late witness values

From the repository root, with C++17, Boost headers, and Python 3:

```sh
mkdir -p /tmp/mertens-extension
c++ -O3 -std=c++17 experiments/mertens_finite_extension/finite_certificate.cpp -o /tmp/mertens-extension/predict
/tmp/mertens-extension/predict /tmp/mertens-extension > /tmp/mertens-extension/certificates_summary.json
python3 experiments/mertens_finite_extension/verify_certificate.py /tmp/mertens-extension
```

The predictor sieves ONLY mu(1)..mu(1000) for the two interval certificates. Anchors beyond this prefix use the bilinear floor identity. Its separate late witnesses sieve ONLY through 5547. The Python checker independently sieves the full certificate interval and verifies every anchor, every integer power floor and every contiguous guard. It checks the late witnesses' power arithmetic, not their Mobius values; independent full-census comparison supplied those in the research run.

Expected: 5167 anchors at exponent 9/20 and 1981 at 51/100, each covering every new integer from 1001 through 1002000. The checked-in JSON records these results and the exact power differences at n=30770120 and n=30770121. Floating-point estimates seed searches only; exact arbitrary-precision integer comparisons correct the searches and decide all envelope tests. A positive witness gap means abs(M(n))^20>n^9.

The Lean general lift and interval-guard proofs are in research/MERTENS_FINITE_PREFIX_EXTENSION.lean. The optimized C++ floor-sum implementation and numerical CSV data are not asserted to have been kernel-verified. See the research Markdown for the unproved all-scale invariant and the absolute-defect obstruction.
