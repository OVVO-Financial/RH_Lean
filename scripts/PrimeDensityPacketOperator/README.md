# Prime-density packet-operator reproducibility

> **Correction after PR #99:** `prime_density_packet_operator.py` implements the historical midpoint-lifetime model. Its exact packet-start and recombination checks remain valid, and its aggregate prediction remains a useful finite diagnostic. Its cofactor-resolved rank, diagonal, and Mellin structure are **not canonical**: later tests show those features are dominated by the deterministic midpoint-lifetime mismatch.

The corrected exact-activity diagnostics live in `../ExactActivityPrimeVariance/` and are described in:

- `../../research/PRIME_DENSITY_PACKET_OPERATOR.md`;
- `../../research/PR99_CORRECTION_EXACT_ACTIVITY.md`.

## Historical run

```bash
python prime_density_packet_operator.py \
  --nmax 10000 \
  --identity-nmax 4000 \
  --output prime_density_packet_operator_N10000.json
```

Dependencies:

```text
numpy
numba
```

The default run sieves through

```text
(10000 + 1)^2 - 1 = 100020000
```

and may require substantial memory.

## What remains exact

The script checks, with integer error zero:

- complete odd-annulus reconstruction of the square-prefix Mertens sequence;
- the cofactor/short-prime-interval formula for packet starts through `identity_nmax`;
- the algebraic recombination

  ```text
  S = (L + H_hat_mid) + (H - H_hat_mid).
  ```

## Historical numerical evidence

The following remain finite diagnostics of the midpoint-lifetime approximation, not asymptotic theorems:

- packet-bias prediction accuracy;
- aggregate correlation of the midpoint model and exact high process;
- normalized local energies over the reported finite windows.

Do not use this model's cofactor-row diagonal, singular vectors, or Mellin projections as properties of the exact prime discrepancy. Use the exact-activity suite instead.
