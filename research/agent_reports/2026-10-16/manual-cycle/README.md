# Reproducers — unified manual research cycle, 2026-10-16

Run `RH-UNIFIED-MANUAL-20261016T0806-0400` (one owner-requested AI session performing the seven RH_Lean functions sequentially). These files are finite computations and executable reproducers, **not** Lean certificates or proofs of any all-scale statement. The proofs are in the dated role reports (`10-owner-payment.md`, `20-analytic-type-ii.md`, and the manual sections of `30`–`60`).

| File | Purpose | sha256 |
| --- | --- | --- |
| `ledger_lab.cpp` | raw odd-seat ledger for all `R <= Rmax`: greatest-prime tag sectors S1..S4, T/H splits, band identity terms, per-tag `eta` bracket check, A/B cut-mode bookkeeping, per-seat strata | `c5346e6c…e963` |
| `ledger5000.csv.gz` | output for `R = 3..5000` (gzip; uncompressed sha256 `dbb8cd43…f926`) | — |
| `PREREGISTRATION.md` | predictions and rejection rules written before evaluating `R in [1000, 5000]` | `9ebfd820…a522da` |
| `evaluate.py` / `evaluate_out.txt` | evaluation of the pre-registered predictions | `741cea8c…61ec` / `6e5520a5…93c7` |
| `crosscheck_small.py` / `crosscheck_out.txt` | independent exact-factoring Python check, `6 <= R <= 300`, incl. direct complete-fibre check | `cc79fac7…0b5d` / `91ad23a4…193e` |
| `detail_R*.txt` | per-seat strata (sector × Omega, sector × cofactor exponent) recomputed directly | — |
| `band_mode_large.cpp` / `band_large.csv.gz` / `band_large_summary.txt` | `F_R (E(2R-1) - E(R-1))` for 5,489 roots up to `10^9` (primes sieved to `2*10^9`) | `7b51a221…2533` / unc. `bc9da5f1…e19444` / `d0ee3b1f…29f9` |
| `mulift_anatomy.cpp` / `mulift_anatomy.csv` | exact floor-kernel anatomy `M(X) = 2M(N) + K1 - K2 + K3` at `N = 10^3, 3162, 10^4` | `97878296…dd64` / `550e1cdd…608a` |

Commands:

```text
g++ -O2 -std=c++20 ledger_lab.cpp -o ledger_lab
./ledger_lab 600 ledger600.csv 500
./ledger_lab 5000 ledger5000.csv 2500,3162,4096,4999,5000
python3 evaluate.py
python3 -I crosscheck_small.py ledger600.csv 300        # needs mpmath
g++ -O2 -std=c++20 band_mode_large.cpp -o band_mode_large && ./band_mode_large 1000000000 band_large.csv
g++ -O2 -std=c++20 mulift_anatomy.cpp -o mulift_anatomy && ./mulift_anatomy > mulift_anatomy.csv
```

Environment: g++ 13.3.0, Python 3.13.16, mpmath. Integer populations are exact; weights are long double; no certified intervals.
