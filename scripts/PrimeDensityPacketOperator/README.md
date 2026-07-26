# Prime-density packet-operator reproducibility

This directory contains one self-contained numerical test for the exact dyadic odd-annulus framework.

## Run

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

## What is exact

The script checks, with integer error zero:

- complete odd-annulus reconstruction of the square-prefix Mertens sequence;
- the cofactor/short-prime-interval formula for packet starts through `identity_nmax`;
- the algebraic recombination

  ```text
  S = (L + H_hat) + (H - H_hat).
  ```

## What is only numerical evidence

The following are finite diagnostics, not proved asymptotic estimates:

- accuracy of the local prime-density packet-bias prediction;
- correlation of the modeled and exact high packet processes;
- normalized local energies and fitted growth slopes.

See `../../research/PRIME_DENSITY_PACKET_OPERATOR.md` for the proof-facing interpretation and the two remaining analytic obligations.
