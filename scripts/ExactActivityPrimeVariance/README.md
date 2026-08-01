# Exact-activity prime-variance diagnostics

This directory corrects the midpoint-lifetime interpretation introduced in PR #99.

## Canonical interval

For time `t` and odd cofactor `c`, the exact active-prime interval is

```text
L(t,c) = max(t+2, ceil((t+1)^2/(2c)))
U(t,c) = floor(((t+1)^2-1)/c).
```

The exact high contribution is the signed prime count on this interval. The deterministic model integrates `1/log(q)` over the same interval.

## Script

```bash
python exact_activity_residual.py \
  --mode all \
  --output exact_activity_residual_results.json
```

The script provides two diagnostics:

1. `split`: separates the historical midpoint residual into the pure prime-count discrepancy and the deterministic lifetime mismatch;
2. `scaling`: measures dyadic-band sign-blind and signed energies of the pure exact-activity prime discrepancy through the requested scales.

For a quick validation run:

```bash
python exact_activity_residual.py \
  --mode split \
  --split-n 1000 \
  --split-lo 512 \
  --split-hi 1024 \
  --output smoke.json
```

## Dependencies

```text
numpy
numba
```

## Classification

- exact: interval endpoints, finite prime counts, and matrix recombination identities;
- finite evidence: scaling fits over requested finite ranges;
- open: every uniform asymptotic variance estimate and every RH implication.

See `../../research/PRIME_DENSITY_PACKET_OPERATOR.md` and `../../research/PR99_CORRECTION_EXACT_ACTIVITY.md`.
