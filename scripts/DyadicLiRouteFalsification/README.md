# Dyadic Li-route falsification suite

This directory reproduces the finite diagnostics recorded in
`research/DYADIC_LI_ROUTE_FALSIFICATION.md`.

The scripts use exact prime-count tables and exact active-prime endpoints, with
`Li(x) = Ei(log x)` as the baseline. They are diagnostics, not theorem
certificates and not asymptotic evidence by themselves.

## Dependencies

```bash
python -m pip install numpy pandas scipy numba
```

## Runs

Primary Möbius-versus-random grid:

```bash
python scripts/DyadicLiRouteFalsification/validate_or_kill_kj.py
```

Coherent/centered refinement:

```bash
python scripts/DyadicLiRouteFalsification/refine_kj_coherent_test.py
```

Full complementary-main/paired/tail recombination:

```bash
python scripts/DyadicLiRouteFalsification/full_recombination_validation.py
```

Exact-cancellation and span diagnostic:

```bash
python scripts/DyadicLiRouteFalsification/exact_cancellation_diagnostic.py
```

All scripts write into
`scripts/DyadicLiRouteFalsification/results/` unless `--outdir` is supplied by
the primary script.

## Retained result tables

- `kj_falsification_grid.csv`
- `kj_falsification_summary.csv`
- `kj_scale_trends.csv`
- `kj_coherent_centered_grid.csv`
- `kj_coherent_centered_summary.csv`
- `full_recombination_grid.csv`
- `exact_cancellation_window_tests.csv`
- `exact_cancellation_svd_tests.csv`

The per-time profile CSV files and plots are regenerated rather than retained
in the repository.
