# Numerical reproducibility

This directory contains deterministic numerical material referenced by the paper. These computations are diagnostics and reproducibility checks; they are not premises of the Lean theorems.

## Main paper run

```bash
python -m pip install -r requirements.txt
python squared_space_reproducibility_v3.py \
  --nmax 4096 \
  --out results/squared_space_repro_v2
```

The script reports exact integer identity checks and writes the CSV diagnostics named in its module docstring.

## Analytic falsification gates

```bash
python analytic_kill_gates.py \
  --nmax 4096 \
  --boundary-mmax 2048 \
  --rmax 240 \
  --cutoff 60 \
  --lambda-high 16 \
  --out results/analytic_gate_results
```

The gates are explicitly diagnostic. In particular, reduced-mode inventories are not projection-norm proofs and do not establish the remaining maximal nonconcentration estimate.

## Reproducibility record

The original sandbox did not contain a committed generated-output directory or fixed Python lockfile. The public workflow records package versions in each run and uploads all generated outputs as a GitHub Actions artifact. After selecting a release environment, commit a lockfile and release archive with `SHA256SUMS.txt` if permanent byte-for-byte reproduction is required.
