# Localized Mobius square-shell moving-window census

**Date:** 2026-10-18. **Evidence:** exact finite arithmetic and randomized finite diagnostics; no uniform quantitative Mobius, VF, or RH claim.

The [research report](../../research/LOCALIZED_MOBIUS_MOVING_WINDOW_CENSUS_20261018.md) gives the derivations, finite values, validation methodology, and caveats.

## Exact carrier

For H <= r < 2H, define delta_r = sum(j=1..2r) mu(r^2+j), S_r(t) = sum(j=1..2r) mu(r^2+t+j), E(H) = sum(delta_r^2), W(H;T) = sum(r,t) S_r(t)^2 for -T <= t <= T. At t=0 both square endpoints are excluded. Let D be sum of mu(n)^2 over all translated windows; 2C=W-D is the exact signed off-diagonal term.

Translated energy decomposes exactly into (2T+1)*sum_r mean_t(S_r(t))^2 plus the nonnegative centered variation sum.

## Frozen evidence

- [37-row census](data/window_results_H8192.csv): dyadic H=64 through 8192, radii T=floor(H^beta) for beta=1/2, 2/3, 3/4, 7/8 and T=H/2 (duplicates omitted). Integer E,W,D,offdiag and core/cross/edge fields are exact.
- [Finite optimal-radius results](data/window_optimal_T.csv): best deterministic upper bound at each H over all integer 1<=T<=H/2.
- [Fixed-squarefree-support randomized controls](data/squarefree_null_H4096.csv): genuine signs in row 0 plus 48 independently seeded pseudorandom sign replicates, preserving every squareful-zero site and each diagonal.

H=4096, T=512: E=30,291,950; W=30,892,995,718; W/D=0.985095; 97.261% of energy in translation mean.
Held-out H=8192, T=861: E=126,589,560; W=218,434,508,977; W/D=1.035860; 97.735% of energy in translation mean.

## Reproduction from repository root

```sh
python3 experiments/mobius_moving_windows/check_data.py
g++ -O3 -std=c++17 -Wall -Wextra -Werror experiments/mobius_moving_windows/reproduce_one_block.cpp -o /tmp/mw_census
python3 experiments/mobius_moving_windows/check_data.py --binary /tmp/mw_census
/tmp/mw_census 4096 512
/tmp/mw_census 8192 861
```

The default CI smoke reruns H=64,T=22 and H=256,T=64 and checks frozen integer invariants. H=8192 uses roughly 2.31 GiB peak resident memory and is opt-in. The concise reproducer is independently coded from the exact Mobius definition; it recovers principal E,W,D, signed delta, and mean-mode measurements. The 48-control data are frozen results from the original full experiment and are not rerun in light CI.

## Interpretation and open gate

The deterministic Lipschitz envelope gives E(H) <= W(H;T)/T + (4/3)*H*(T*T-1) for integer T>=1. Finite falling values of W/H^(13/4) at T=floor(H^(3/4)) do not prove an asymptotic bound. Although the integer-site translation Gram kernel has rank 2T+1, more than 97% of energy lies in the constant translation mode at the largest tested H; signed off-diagonal covariance changes sign across blocks. A genuine independently proved all-scale saving on the complete W, including its constant mode, remains OPEN. Original VF #915 payment, finite A/C, canonical pi-VF, and RH remain open.
