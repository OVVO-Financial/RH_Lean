# Exact cofactor-conditioned prime availability and shared ancestry

This directory reproduces the **finite** 2026-10-11 experiment documented in
[the research note](../../research/COFACTOR_CONDITIONAL_PRIME_AVAILABILITY_GCD_FINITE_C_2026_10_11.md).

It uses actual Euler–Möbius coefficients, actual primes and integer-accurate
incidence and signed-energy sums, **not** random prime assignments. The main
C++ executable scans *every* root `2 <= R <= 6000` by default and independently
reconstructs the historical finite-C kernel, conditional parity exposures,
the same-prime cofactor-overlap Gram, and gcd-stratified cross terms. Six roots
also receive complete smooth/high signed factor-depth and owner accounting.

Run in this directory:

```sh
g++ -O3 -std=c++17 -Wall -Wextra cofactor_conditioning_census.cpp -o census
./census 6000 .
python3 -m pip install pandas numpy matplotlib
python3 plot_results.py
python3 analyze_results.py
```

For a quick check, `./census 317 .` also runs the complete physical pair
cross-check at root 56, and audits the 56 and 317 endpoint reconstructions.
The C++ source uses only the C++17 standard library; optional figures and
tabular summaries require Python with pandas, numpy and matplotlib. Output
is written to the directory supplied as the **second** executable argument,
defaulting to the current directory.

Generated CSVs:

- `root_features.csv`: every root, genuine prime-extension counts,
  conditional CDF sign-crossings and the exact shared/coprime gcd Gram.
- `selected_owner_groups.csv`, `selected_depth.csv`,
  `selected_dyadic.csv`: occurrence-preserving signed populations.
- `selected_gcd_overlap.csv`: explicit same-prime pair census by gcd stratum.
- `selected_smooth_high_gcd.csv`: smooth/high cross-energy split via exact
  Möbius coprimality inversion.
- `selected_prime_updates.csv`: independent post-root prime-comb updates.

The four figures are recreated by `plot_results.py`.
The earlier `prime_phase_experiment/actual_root_scan.csv` independently agrees
at all 5,999 integer root entries when scanning through 6000.

**Proof status:** finite identities and reproducible exact integer census.
The observed negative shared-gcd term has not been proved for all roots;
neither finite C, finite A nor RH has been established.
